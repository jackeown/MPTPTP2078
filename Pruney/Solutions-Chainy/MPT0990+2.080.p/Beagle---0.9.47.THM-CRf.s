%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:07 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.14s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 818 expanded)
%              Number of leaves         :   43 ( 309 expanded)
%              Depth                    :   17
%              Number of atoms          :  323 (3689 expanded)
%              Number of equality atoms :   99 (1350 expanded)
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
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

tff(f_103,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_99,axiom,(
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

tff(f_115,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_53,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_71,axiom,(
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

tff(c_98,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_98])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_194,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_207,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_194])).

tff(c_2128,plain,(
    ! [B_162,C_163,A_164] :
      ( k6_partfun1(B_162) = k5_relat_1(k2_funct_1(C_163),C_163)
      | k1_xboole_0 = B_162
      | ~ v2_funct_1(C_163)
      | k2_relset_1(A_164,B_162,C_163) != B_162
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_162)))
      | ~ v1_funct_2(C_163,A_164,B_162)
      | ~ v1_funct_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2134,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_2128])).

tff(c_2144,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_207,c_2134])).

tff(c_2145,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2144])).

tff(c_2160,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2145])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_34,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_183,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_relset_1(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_190,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_34,c_183])).

tff(c_959,plain,(
    ! [E_108,B_107,A_109,C_111,F_110,D_106] :
      ( k1_partfun1(A_109,B_107,C_111,D_106,E_108,F_110) = k5_relat_1(E_108,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_111,D_106)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_965,plain,(
    ! [A_109,B_107,E_108] :
      ( k1_partfun1(A_109,B_107,'#skF_2','#skF_1',E_108,'#skF_4') = k5_relat_1(E_108,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(resolution,[status(thm)],[c_66,c_959])).

tff(c_1377,plain,(
    ! [A_125,B_126,E_127] :
      ( k1_partfun1(A_125,B_126,'#skF_2','#skF_1',E_127,'#skF_4') = k5_relat_1(E_127,'#skF_4')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_965])).

tff(c_1383,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1377])).

tff(c_1390,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1383])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_533,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_541,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_533])).

tff(c_556,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_541])).

tff(c_573,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_1470,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_573])).

tff(c_1476,plain,(
    ! [C_128,B_129,A_132,E_130,D_133,F_131] :
      ( m1_subset_1(k1_partfun1(A_132,B_129,C_128,D_133,E_130,F_131),k1_zfmisc_1(k2_zfmisc_1(A_132,D_133)))
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_128,D_133)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1504,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_1476])).

tff(c_1516,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1504])).

tff(c_1522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1470,c_1516])).

tff(c_1523,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_3045,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( k2_relset_1(A_198,B_199,C_200) = B_199
      | ~ r2_relset_1(B_199,B_199,k1_partfun1(B_199,A_198,A_198,B_199,D_201,C_200),k6_partfun1(B_199))
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(B_199,A_198)))
      | ~ v1_funct_2(D_201,B_199,A_198)
      | ~ v1_funct_1(D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_2(C_200,A_198,B_199)
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3051,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_3045])).

tff(c_3055,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_190,c_207,c_3051])).

tff(c_3057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2160,c_3055])).

tff(c_3058,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2145])).

tff(c_3098,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3058])).

tff(c_38,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12,plain,(
    ! [A_11] : v2_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    ! [A_11] : v2_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_4161,plain,(
    ! [E_242,A_245,D_244,C_243,B_246] :
      ( k1_xboole_0 = C_243
      | v2_funct_1(E_242)
      | k2_relset_1(A_245,B_246,D_244) != B_246
      | ~ v2_funct_1(k1_partfun1(A_245,B_246,B_246,C_243,D_244,E_242))
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(B_246,C_243)))
      | ~ v1_funct_2(E_242,B_246,C_243)
      | ~ v1_funct_1(E_242)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ v1_funct_2(D_244,A_245,B_246)
      | ~ v1_funct_1(D_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4165,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_4161])).

tff(c_4170,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_77,c_64,c_4165])).

tff(c_4172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3098,c_58,c_4170])).

tff(c_4174,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3058])).

tff(c_10,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3059,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2145])).

tff(c_3060,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3059,c_207])).

tff(c_4276,plain,(
    ! [A_250,C_251,B_252] :
      ( k6_partfun1(A_250) = k5_relat_1(C_251,k2_funct_1(C_251))
      | k1_xboole_0 = B_252
      | ~ v2_funct_1(C_251)
      | k2_relset_1(A_250,B_252,C_251) != B_252
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_250,B_252)))
      | ~ v1_funct_2(C_251,A_250,B_252)
      | ~ v1_funct_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_4282,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4276])).

tff(c_4292,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_3060,c_4174,c_4282])).

tff(c_4293,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4292])).

tff(c_108,plain,(
    ! [A_30] : v1_relat_1(k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_4,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),A_8) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_225,plain,(
    ! [A_75,B_76,C_77] :
      ( k5_relat_1(k5_relat_1(A_75,B_76),C_77) = k5_relat_1(A_75,k5_relat_1(B_76,C_77))
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_254,plain,(
    ! [A_8,C_77] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_77)) = k5_relat_1(A_8,C_77)
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(A_8)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_225])).

tff(c_266,plain,(
    ! [A_8,C_77] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_8)),k5_relat_1(A_8,C_77)) = k5_relat_1(A_8,C_77)
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_254])).

tff(c_4323,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4293,c_266])).

tff(c_4330,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_4293,c_4323])).

tff(c_4759,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4330])).

tff(c_4762,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_4759])).

tff(c_4766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_70,c_4762])).

tff(c_4768,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4330])).

tff(c_109,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_98])).

tff(c_200,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_194])).

tff(c_206,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_200])).

tff(c_6,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_relat_1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k6_partfun1(k2_relat_1(A_9))) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_211,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_78])).

tff(c_215,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_211])).

tff(c_168,plain,(
    ! [A_67] :
      ( k1_relat_1(k2_funct_1(A_67)) = k2_relat_1(A_67)
      | ~ v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5180,plain,(
    ! [A_286] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_286)),k2_funct_1(A_286)) = k2_funct_1(A_286)
      | ~ v1_relat_1(k2_funct_1(A_286))
      | ~ v2_funct_1(A_286)
      | ~ v1_funct_1(A_286)
      | ~ v1_relat_1(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_79])).

tff(c_5206,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3059,c_5180])).

tff(c_5230,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_70,c_4174,c_4768,c_5206])).

tff(c_1917,plain,(
    ! [A_152,B_150,F_153,C_154,D_149,E_151] :
      ( k1_partfun1(A_152,B_150,C_154,D_149,E_151,F_153) = k5_relat_1(E_151,F_153)
      | ~ m1_subset_1(F_153,k1_zfmisc_1(k2_zfmisc_1(C_154,D_149)))
      | ~ v1_funct_1(F_153)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1923,plain,(
    ! [A_152,B_150,E_151] :
      ( k1_partfun1(A_152,B_150,'#skF_2','#skF_1',E_151,'#skF_4') = k5_relat_1(E_151,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(resolution,[status(thm)],[c_66,c_1917])).

tff(c_4349,plain,(
    ! [A_253,B_254,E_255] :
      ( k1_partfun1(A_253,B_254,'#skF_2','#skF_1',E_255,'#skF_4') = k5_relat_1(E_255,'#skF_4')
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ v1_funct_1(E_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1923])).

tff(c_4355,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4349])).

tff(c_4362,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1523,c_4355])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4381,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4362,c_2])).

tff(c_4393,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_110,c_4381])).

tff(c_5236,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5230,c_4393])).

tff(c_5252,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4768,c_215,c_4293,c_5236])).

tff(c_18,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5285,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5252,c_18])).

tff(c_5303,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_70,c_4174,c_5285])).

tff(c_5305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.14/2.42  
% 7.14/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.14/2.42  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.14/2.42  
% 7.14/2.42  %Foreground sorts:
% 7.14/2.42  
% 7.14/2.42  
% 7.14/2.42  %Background operators:
% 7.14/2.42  
% 7.14/2.42  
% 7.14/2.42  %Foreground operators:
% 7.14/2.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.14/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.14/2.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.14/2.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.14/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.14/2.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.14/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.14/2.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.14/2.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.14/2.42  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.14/2.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.14/2.42  tff('#skF_2', type, '#skF_2': $i).
% 7.14/2.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.14/2.42  tff('#skF_3', type, '#skF_3': $i).
% 7.14/2.42  tff('#skF_1', type, '#skF_1': $i).
% 7.14/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.14/2.42  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.14/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.14/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.14/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.14/2.42  tff('#skF_4', type, '#skF_4': $i).
% 7.14/2.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.14/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.14/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.14/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.14/2.42  
% 7.14/2.45  tff(f_200, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.14/2.45  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.14/2.45  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.14/2.45  tff(f_174, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.14/2.45  tff(f_103, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.14/2.45  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.14/2.45  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.14/2.45  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.14/2.45  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.14/2.45  tff(f_115, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.14/2.45  tff(f_53, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 7.14/2.45  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.14/2.45  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.14/2.45  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 7.14/2.45  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.14/2.45  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.14/2.45  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.14/2.45  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 7.14/2.45  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_98, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.14/2.45  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_98])).
% 7.14/2.45  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_194, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.14/2.45  tff(c_207, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_194])).
% 7.14/2.45  tff(c_2128, plain, (![B_162, C_163, A_164]: (k6_partfun1(B_162)=k5_relat_1(k2_funct_1(C_163), C_163) | k1_xboole_0=B_162 | ~v2_funct_1(C_163) | k2_relset_1(A_164, B_162, C_163)!=B_162 | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_162))) | ~v1_funct_2(C_163, A_164, B_162) | ~v1_funct_1(C_163))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.14/2.45  tff(c_2134, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_2128])).
% 7.14/2.45  tff(c_2144, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_207, c_2134])).
% 7.14/2.45  tff(c_2145, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_2144])).
% 7.14/2.45  tff(c_2160, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2145])).
% 7.14/2.45  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_34, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.14/2.45  tff(c_183, plain, (![A_68, B_69, D_70]: (r2_relset_1(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.14/2.45  tff(c_190, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_34, c_183])).
% 7.14/2.45  tff(c_959, plain, (![E_108, B_107, A_109, C_111, F_110, D_106]: (k1_partfun1(A_109, B_107, C_111, D_106, E_108, F_110)=k5_relat_1(E_108, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_111, D_106))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_107))) | ~v1_funct_1(E_108))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.14/2.45  tff(c_965, plain, (![A_109, B_107, E_108]: (k1_partfun1(A_109, B_107, '#skF_2', '#skF_1', E_108, '#skF_4')=k5_relat_1(E_108, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_107))) | ~v1_funct_1(E_108))), inference(resolution, [status(thm)], [c_66, c_959])).
% 7.14/2.45  tff(c_1377, plain, (![A_125, B_126, E_127]: (k1_partfun1(A_125, B_126, '#skF_2', '#skF_1', E_127, '#skF_4')=k5_relat_1(E_127, '#skF_4') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_1(E_127))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_965])).
% 7.14/2.45  tff(c_1383, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1377])).
% 7.14/2.45  tff(c_1390, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1383])).
% 7.14/2.45  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_533, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.14/2.45  tff(c_541, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_533])).
% 7.14/2.45  tff(c_556, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_541])).
% 7.14/2.45  tff(c_573, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_556])).
% 7.14/2.45  tff(c_1470, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_573])).
% 7.14/2.45  tff(c_1476, plain, (![C_128, B_129, A_132, E_130, D_133, F_131]: (m1_subset_1(k1_partfun1(A_132, B_129, C_128, D_133, E_130, F_131), k1_zfmisc_1(k2_zfmisc_1(A_132, D_133))) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_128, D_133))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_129))) | ~v1_funct_1(E_130))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.14/2.45  tff(c_1504, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1390, c_1476])).
% 7.14/2.45  tff(c_1516, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1504])).
% 7.14/2.45  tff(c_1522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1470, c_1516])).
% 7.14/2.45  tff(c_1523, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_556])).
% 7.14/2.45  tff(c_3045, plain, (![A_198, B_199, C_200, D_201]: (k2_relset_1(A_198, B_199, C_200)=B_199 | ~r2_relset_1(B_199, B_199, k1_partfun1(B_199, A_198, A_198, B_199, D_201, C_200), k6_partfun1(B_199)) | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(B_199, A_198))) | ~v1_funct_2(D_201, B_199, A_198) | ~v1_funct_1(D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_2(C_200, A_198, B_199) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.14/2.45  tff(c_3051, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1523, c_3045])).
% 7.14/2.45  tff(c_3055, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_190, c_207, c_3051])).
% 7.14/2.45  tff(c_3057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2160, c_3055])).
% 7.14/2.45  tff(c_3058, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2145])).
% 7.14/2.45  tff(c_3098, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3058])).
% 7.14/2.45  tff(c_38, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.14/2.45  tff(c_12, plain, (![A_11]: (v2_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.14/2.45  tff(c_77, plain, (![A_11]: (v2_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 7.14/2.45  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_200])).
% 7.14/2.45  tff(c_4161, plain, (![E_242, A_245, D_244, C_243, B_246]: (k1_xboole_0=C_243 | v2_funct_1(E_242) | k2_relset_1(A_245, B_246, D_244)!=B_246 | ~v2_funct_1(k1_partfun1(A_245, B_246, B_246, C_243, D_244, E_242)) | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(B_246, C_243))) | ~v1_funct_2(E_242, B_246, C_243) | ~v1_funct_1(E_242) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~v1_funct_2(D_244, A_245, B_246) | ~v1_funct_1(D_244))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.14/2.45  tff(c_4165, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1523, c_4161])).
% 7.14/2.45  tff(c_4170, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_77, c_64, c_4165])).
% 7.14/2.45  tff(c_4172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3098, c_58, c_4170])).
% 7.14/2.45  tff(c_4174, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3058])).
% 7.14/2.45  tff(c_10, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.14/2.45  tff(c_3059, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2145])).
% 7.14/2.45  tff(c_3060, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3059, c_207])).
% 7.14/2.45  tff(c_4276, plain, (![A_250, C_251, B_252]: (k6_partfun1(A_250)=k5_relat_1(C_251, k2_funct_1(C_251)) | k1_xboole_0=B_252 | ~v2_funct_1(C_251) | k2_relset_1(A_250, B_252, C_251)!=B_252 | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_250, B_252))) | ~v1_funct_2(C_251, A_250, B_252) | ~v1_funct_1(C_251))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.14/2.45  tff(c_4282, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_4276])).
% 7.14/2.45  tff(c_4292, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_3060, c_4174, c_4282])).
% 7.14/2.45  tff(c_4293, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_4292])).
% 7.14/2.45  tff(c_108, plain, (![A_30]: (v1_relat_1(k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_34, c_98])).
% 7.14/2.45  tff(c_4, plain, (![A_8]: (k5_relat_1(k6_relat_1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.14/2.45  tff(c_79, plain, (![A_8]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), A_8)=A_8 | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4])).
% 7.14/2.45  tff(c_225, plain, (![A_75, B_76, C_77]: (k5_relat_1(k5_relat_1(A_75, B_76), C_77)=k5_relat_1(A_75, k5_relat_1(B_76, C_77)) | ~v1_relat_1(C_77) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.14/2.45  tff(c_254, plain, (![A_8, C_77]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_77))=k5_relat_1(A_8, C_77) | ~v1_relat_1(C_77) | ~v1_relat_1(A_8) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_79, c_225])).
% 7.14/2.45  tff(c_266, plain, (![A_8, C_77]: (k5_relat_1(k6_partfun1(k1_relat_1(A_8)), k5_relat_1(A_8, C_77))=k5_relat_1(A_8, C_77) | ~v1_relat_1(C_77) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_254])).
% 7.14/2.45  tff(c_4323, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4293, c_266])).
% 7.14/2.45  tff(c_4330, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_4293, c_4323])).
% 7.14/2.45  tff(c_4759, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4330])).
% 7.14/2.45  tff(c_4762, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_4759])).
% 7.14/2.45  tff(c_4766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_70, c_4762])).
% 7.14/2.45  tff(c_4768, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4330])).
% 7.14/2.45  tff(c_109, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_98])).
% 7.14/2.45  tff(c_200, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_194])).
% 7.14/2.45  tff(c_206, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_200])).
% 7.14/2.45  tff(c_6, plain, (![A_9]: (k5_relat_1(A_9, k6_relat_1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.14/2.45  tff(c_78, plain, (![A_9]: (k5_relat_1(A_9, k6_partfun1(k2_relat_1(A_9)))=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6])).
% 7.14/2.45  tff(c_211, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_206, c_78])).
% 7.14/2.45  tff(c_215, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_211])).
% 7.14/2.45  tff(c_168, plain, (![A_67]: (k1_relat_1(k2_funct_1(A_67))=k2_relat_1(A_67) | ~v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.14/2.45  tff(c_5180, plain, (![A_286]: (k5_relat_1(k6_partfun1(k2_relat_1(A_286)), k2_funct_1(A_286))=k2_funct_1(A_286) | ~v1_relat_1(k2_funct_1(A_286)) | ~v2_funct_1(A_286) | ~v1_funct_1(A_286) | ~v1_relat_1(A_286))), inference(superposition, [status(thm), theory('equality')], [c_168, c_79])).
% 7.14/2.45  tff(c_5206, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3059, c_5180])).
% 7.14/2.45  tff(c_5230, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_70, c_4174, c_4768, c_5206])).
% 7.14/2.45  tff(c_1917, plain, (![A_152, B_150, F_153, C_154, D_149, E_151]: (k1_partfun1(A_152, B_150, C_154, D_149, E_151, F_153)=k5_relat_1(E_151, F_153) | ~m1_subset_1(F_153, k1_zfmisc_1(k2_zfmisc_1(C_154, D_149))) | ~v1_funct_1(F_153) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_150))) | ~v1_funct_1(E_151))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.14/2.45  tff(c_1923, plain, (![A_152, B_150, E_151]: (k1_partfun1(A_152, B_150, '#skF_2', '#skF_1', E_151, '#skF_4')=k5_relat_1(E_151, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_150))) | ~v1_funct_1(E_151))), inference(resolution, [status(thm)], [c_66, c_1917])).
% 7.14/2.45  tff(c_4349, plain, (![A_253, B_254, E_255]: (k1_partfun1(A_253, B_254, '#skF_2', '#skF_1', E_255, '#skF_4')=k5_relat_1(E_255, '#skF_4') | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~v1_funct_1(E_255))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1923])).
% 7.14/2.45  tff(c_4355, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_4349])).
% 7.14/2.45  tff(c_4362, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1523, c_4355])).
% 7.14/2.45  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.14/2.45  tff(c_4381, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4362, c_2])).
% 7.14/2.45  tff(c_4393, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_110, c_4381])).
% 7.14/2.45  tff(c_5236, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5230, c_4393])).
% 7.14/2.45  tff(c_5252, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4768, c_215, c_4293, c_5236])).
% 7.14/2.45  tff(c_18, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.14/2.45  tff(c_5285, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5252, c_18])).
% 7.14/2.45  tff(c_5303, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_70, c_4174, c_5285])).
% 7.14/2.45  tff(c_5305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5303])).
% 7.14/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.14/2.45  
% 7.14/2.45  Inference rules
% 7.14/2.45  ----------------------
% 7.14/2.45  #Ref     : 0
% 7.14/2.45  #Sup     : 1161
% 7.14/2.45  #Fact    : 0
% 7.14/2.45  #Define  : 0
% 7.14/2.45  #Split   : 17
% 7.14/2.45  #Chain   : 0
% 7.14/2.45  #Close   : 0
% 7.14/2.45  
% 7.14/2.45  Ordering : KBO
% 7.14/2.45  
% 7.14/2.45  Simplification rules
% 7.14/2.45  ----------------------
% 7.14/2.45  #Subsume      : 31
% 7.14/2.45  #Demod        : 1648
% 7.14/2.45  #Tautology    : 529
% 7.14/2.45  #SimpNegUnit  : 45
% 7.14/2.45  #BackRed      : 23
% 7.14/2.45  
% 7.14/2.45  #Partial instantiations: 0
% 7.14/2.45  #Strategies tried      : 1
% 7.14/2.45  
% 7.14/2.45  Timing (in seconds)
% 7.14/2.45  ----------------------
% 7.14/2.45  Preprocessing        : 0.38
% 7.14/2.45  Parsing              : 0.21
% 7.14/2.45  CNF conversion       : 0.03
% 7.14/2.45  Main loop            : 1.28
% 7.14/2.45  Inferencing          : 0.45
% 7.14/2.45  Reduction            : 0.50
% 7.14/2.45  Demodulation         : 0.38
% 7.14/2.45  BG Simplification    : 0.05
% 7.14/2.45  Subsumption          : 0.20
% 7.14/2.45  Abstraction          : 0.06
% 7.14/2.45  MUC search           : 0.00
% 7.14/2.45  Cooper               : 0.00
% 7.14/2.45  Total                : 1.71
% 7.14/2.45  Index Insertion      : 0.00
% 7.14/2.45  Index Deletion       : 0.00
% 7.14/2.45  Index Matching       : 0.00
% 7.14/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
