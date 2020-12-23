%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:24 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 5.08s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 348 expanded)
%              Number of leaves         :   41 ( 144 expanded)
%              Depth                    :   11
%              Number of atoms          :  296 (1492 expanded)
%              Number of equality atoms :   97 ( 498 expanded)
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

tff(f_207,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_181,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_139,axiom,(
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

tff(f_122,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_165,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_119,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_119])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_148,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_160,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_148])).

tff(c_643,plain,(
    ! [A_146,C_147,B_148] :
      ( k6_partfun1(A_146) = k5_relat_1(C_147,k2_funct_1(C_147))
      | k1_xboole_0 = B_148
      | ~ v2_funct_1(C_147)
      | k2_relset_1(A_146,B_148,C_147) != B_148
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_146,B_148)))
      | ~ v1_funct_2(C_147,A_146,B_148)
      | ~ v1_funct_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_647,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_643])).

tff(c_655,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_160,c_647])).

tff(c_656,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_655])).

tff(c_696,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_34,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_138,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_145,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_289,plain,(
    ! [E_99,D_95,B_96,C_100,F_98,A_97] :
      ( k1_partfun1(A_97,B_96,C_100,D_95,E_99,F_98) = k5_relat_1(E_99,F_98)
      | ~ m1_subset_1(F_98,k1_zfmisc_1(k2_zfmisc_1(C_100,D_95)))
      | ~ v1_funct_1(F_98)
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_1(E_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_293,plain,(
    ! [A_97,B_96,E_99] :
      ( k1_partfun1(A_97,B_96,'#skF_2','#skF_1',E_99,'#skF_4') = k5_relat_1(E_99,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_1(E_99) ) ),
    inference(resolution,[status(thm)],[c_66,c_289])).

tff(c_304,plain,(
    ! [A_102,B_103,E_104] :
      ( k1_partfun1(A_102,B_103,'#skF_2','#skF_1',E_104,'#skF_4') = k5_relat_1(E_104,'#skF_4')
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_1(E_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_293])).

tff(c_313,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_304])).

tff(c_320,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_313])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_206,plain,(
    ! [D_74,C_75,A_76,B_77] :
      ( D_74 = C_75
      | ~ r2_relset_1(A_76,B_77,C_75,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_214,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_206])).

tff(c_229,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_214])).

tff(c_239,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_327,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_239])).

tff(c_468,plain,(
    ! [A_116,B_121,D_120,C_117,F_119,E_118] :
      ( m1_subset_1(k1_partfun1(A_116,B_121,C_117,D_120,E_118,F_119),k1_zfmisc_1(k2_zfmisc_1(A_116,D_120)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_117,D_120)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_121)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_505,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_468])).

tff(c_527,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_505])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_527])).

tff(c_530,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_1356,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( k2_relset_1(A_181,B_182,C_183) = B_182
      | ~ r2_relset_1(B_182,B_182,k1_partfun1(B_182,A_181,A_181,B_182,D_184,C_183),k6_partfun1(B_182))
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_182,A_181)))
      | ~ v1_funct_2(D_184,B_182,A_181)
      | ~ v1_funct_1(D_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_2(C_183,A_181,B_182)
      | ~ v1_funct_1(C_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1362,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_1356])).

tff(c_1366,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_145,c_160,c_1362])).

tff(c_1368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_1366])).

tff(c_1369,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_1381,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1369])).

tff(c_38,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_79,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_1906,plain,(
    ! [B_212,A_209,C_210,D_211,E_208] :
      ( k1_xboole_0 = C_210
      | v2_funct_1(E_208)
      | k2_relset_1(A_209,B_212,D_211) != B_212
      | ~ v2_funct_1(k1_partfun1(A_209,B_212,B_212,C_210,D_211,E_208))
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(B_212,C_210)))
      | ~ v1_funct_2(E_208,B_212,C_210)
      | ~ v1_funct_1(E_208)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_212)))
      | ~ v1_funct_2(D_211,A_209,B_212)
      | ~ v1_funct_1(D_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1912,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_530,c_1906])).

tff(c_1920,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_79,c_64,c_1912])).

tff(c_1922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1381,c_58,c_1920])).

tff(c_1924,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1369])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_1923,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1369])).

tff(c_16,plain,(
    ! [A_11] :
      ( k2_relat_1(k5_relat_1(A_11,k2_funct_1(A_11))) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1932,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_16])).

tff(c_1944,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_70,c_1924,c_81,c_1932])).

tff(c_588,plain,(
    ! [C_140,F_138,B_136,A_137,D_135,E_139] :
      ( k1_partfun1(A_137,B_136,C_140,D_135,E_139,F_138) = k5_relat_1(E_139,F_138)
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(C_140,D_135)))
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_592,plain,(
    ! [A_137,B_136,E_139] :
      ( k1_partfun1(A_137,B_136,'#skF_2','#skF_1',E_139,'#skF_4') = k5_relat_1(E_139,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_1(E_139) ) ),
    inference(resolution,[status(thm)],[c_66,c_588])).

tff(c_1960,plain,(
    ! [A_213,B_214,E_215] :
      ( k1_partfun1(A_213,B_214,'#skF_2','#skF_1',E_215,'#skF_4') = k5_relat_1(E_215,'#skF_4')
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214)))
      | ~ v1_funct_1(E_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_592])).

tff(c_1969,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1960])).

tff(c_1976,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_530,c_1969])).

tff(c_128,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_119])).

tff(c_137,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_128])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_157,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_148])).

tff(c_162,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_157])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_649,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_643])).

tff(c_659,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_60,c_649])).

tff(c_660,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_659])).

tff(c_668,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_16])).

tff(c_680,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_76,c_60,c_81,c_668])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k1_relat_1(A_12)) != k5_relat_1(A_12,B_14)
      | k2_relat_1(A_12) != k1_relat_1(B_14)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_partfun1(k1_relat_1(A_12)) != k5_relat_1(A_12,B_14)
      | k2_relat_1(A_12) != k1_relat_1(B_14)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_686,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_3') = B_14
      | k5_relat_1('#skF_3',B_14) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_14)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_77])).

tff(c_2026,plain,(
    ! [B_220] :
      ( k2_funct_1('#skF_3') = B_220
      | k5_relat_1('#skF_3',B_220) != k6_partfun1('#skF_1')
      | k1_relat_1(B_220) != '#skF_2'
      | ~ v1_funct_1(B_220)
      | ~ v1_relat_1(B_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_76,c_60,c_162,c_686])).

tff(c_2032,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_2026])).

tff(c_2044,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1944,c_1976,c_2032])).

tff(c_2046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:24:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.90  
% 5.08/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.90  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.08/1.90  
% 5.08/1.90  %Foreground sorts:
% 5.08/1.90  
% 5.08/1.90  
% 5.08/1.90  %Background operators:
% 5.08/1.90  
% 5.08/1.90  
% 5.08/1.90  %Foreground operators:
% 5.08/1.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.08/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.08/1.90  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.08/1.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.08/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/1.90  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.08/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.08/1.90  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.08/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.08/1.90  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.08/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.08/1.90  tff('#skF_2', type, '#skF_2': $i).
% 5.08/1.90  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.08/1.90  tff('#skF_3', type, '#skF_3': $i).
% 5.08/1.90  tff('#skF_1', type, '#skF_1': $i).
% 5.08/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.08/1.90  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.08/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.08/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.08/1.90  tff('#skF_4', type, '#skF_4': $i).
% 5.08/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.08/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.08/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.08/1.90  
% 5.08/1.93  tff(f_207, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.08/1.93  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.08/1.93  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.08/1.93  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.08/1.93  tff(f_181, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 5.08/1.93  tff(f_110, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.08/1.93  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.08/1.93  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.08/1.93  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.08/1.93  tff(f_139, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.08/1.93  tff(f_122, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.08/1.93  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.08/1.93  tff(f_165, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 5.08/1.93  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.08/1.93  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 5.08/1.93  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 5.08/1.93  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.08/1.93  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_119, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.08/1.93  tff(c_125, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_119])).
% 5.08/1.93  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_125])).
% 5.08/1.93  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_148, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.08/1.93  tff(c_160, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_148])).
% 5.08/1.93  tff(c_643, plain, (![A_146, C_147, B_148]: (k6_partfun1(A_146)=k5_relat_1(C_147, k2_funct_1(C_147)) | k1_xboole_0=B_148 | ~v2_funct_1(C_147) | k2_relset_1(A_146, B_148, C_147)!=B_148 | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_146, B_148))) | ~v1_funct_2(C_147, A_146, B_148) | ~v1_funct_1(C_147))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.08/1.93  tff(c_647, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_643])).
% 5.08/1.93  tff(c_655, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_160, c_647])).
% 5.08/1.93  tff(c_656, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_655])).
% 5.08/1.93  tff(c_696, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_656])).
% 5.08/1.93  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_34, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.08/1.93  tff(c_138, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.08/1.93  tff(c_145, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_34, c_138])).
% 5.08/1.93  tff(c_289, plain, (![E_99, D_95, B_96, C_100, F_98, A_97]: (k1_partfun1(A_97, B_96, C_100, D_95, E_99, F_98)=k5_relat_1(E_99, F_98) | ~m1_subset_1(F_98, k1_zfmisc_1(k2_zfmisc_1(C_100, D_95))) | ~v1_funct_1(F_98) | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_1(E_99))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.08/1.93  tff(c_293, plain, (![A_97, B_96, E_99]: (k1_partfun1(A_97, B_96, '#skF_2', '#skF_1', E_99, '#skF_4')=k5_relat_1(E_99, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_1(E_99))), inference(resolution, [status(thm)], [c_66, c_289])).
% 5.08/1.93  tff(c_304, plain, (![A_102, B_103, E_104]: (k1_partfun1(A_102, B_103, '#skF_2', '#skF_1', E_104, '#skF_4')=k5_relat_1(E_104, '#skF_4') | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_1(E_104))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_293])).
% 5.08/1.93  tff(c_313, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_304])).
% 5.08/1.93  tff(c_320, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_313])).
% 5.08/1.93  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_206, plain, (![D_74, C_75, A_76, B_77]: (D_74=C_75 | ~r2_relset_1(A_76, B_77, C_75, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.08/1.93  tff(c_214, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_206])).
% 5.08/1.93  tff(c_229, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_214])).
% 5.08/1.93  tff(c_239, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_229])).
% 5.08/1.93  tff(c_327, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_239])).
% 5.08/1.93  tff(c_468, plain, (![A_116, B_121, D_120, C_117, F_119, E_118]: (m1_subset_1(k1_partfun1(A_116, B_121, C_117, D_120, E_118, F_119), k1_zfmisc_1(k2_zfmisc_1(A_116, D_120))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_117, D_120))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_121))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.08/1.93  tff(c_505, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_320, c_468])).
% 5.08/1.93  tff(c_527, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_505])).
% 5.08/1.93  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_527])).
% 5.08/1.93  tff(c_530, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_229])).
% 5.08/1.93  tff(c_1356, plain, (![A_181, B_182, C_183, D_184]: (k2_relset_1(A_181, B_182, C_183)=B_182 | ~r2_relset_1(B_182, B_182, k1_partfun1(B_182, A_181, A_181, B_182, D_184, C_183), k6_partfun1(B_182)) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_182, A_181))) | ~v1_funct_2(D_184, B_182, A_181) | ~v1_funct_1(D_184) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_2(C_183, A_181, B_182) | ~v1_funct_1(C_183))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.08/1.93  tff(c_1362, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_530, c_1356])).
% 5.08/1.93  tff(c_1366, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_145, c_160, c_1362])).
% 5.08/1.93  tff(c_1368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_696, c_1366])).
% 5.08/1.93  tff(c_1369, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_656])).
% 5.08/1.93  tff(c_1381, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1369])).
% 5.08/1.93  tff(c_38, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.08/1.93  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.08/1.93  tff(c_79, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 5.08/1.93  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_1906, plain, (![B_212, A_209, C_210, D_211, E_208]: (k1_xboole_0=C_210 | v2_funct_1(E_208) | k2_relset_1(A_209, B_212, D_211)!=B_212 | ~v2_funct_1(k1_partfun1(A_209, B_212, B_212, C_210, D_211, E_208)) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(B_212, C_210))) | ~v1_funct_2(E_208, B_212, C_210) | ~v1_funct_1(E_208) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_212))) | ~v1_funct_2(D_211, A_209, B_212) | ~v1_funct_1(D_211))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.08/1.93  tff(c_1912, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_530, c_1906])).
% 5.08/1.93  tff(c_1920, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_79, c_64, c_1912])).
% 5.08/1.93  tff(c_1922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1381, c_58, c_1920])).
% 5.08/1.93  tff(c_1924, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1369])).
% 5.08/1.93  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.08/1.93  tff(c_81, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8])).
% 5.08/1.93  tff(c_1923, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1369])).
% 5.08/1.93  tff(c_16, plain, (![A_11]: (k2_relat_1(k5_relat_1(A_11, k2_funct_1(A_11)))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.08/1.93  tff(c_1932, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1923, c_16])).
% 5.08/1.93  tff(c_1944, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_70, c_1924, c_81, c_1932])).
% 5.08/1.93  tff(c_588, plain, (![C_140, F_138, B_136, A_137, D_135, E_139]: (k1_partfun1(A_137, B_136, C_140, D_135, E_139, F_138)=k5_relat_1(E_139, F_138) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(C_140, D_135))) | ~v1_funct_1(F_138) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.08/1.93  tff(c_592, plain, (![A_137, B_136, E_139]: (k1_partfun1(A_137, B_136, '#skF_2', '#skF_1', E_139, '#skF_4')=k5_relat_1(E_139, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_1(E_139))), inference(resolution, [status(thm)], [c_66, c_588])).
% 5.08/1.93  tff(c_1960, plain, (![A_213, B_214, E_215]: (k1_partfun1(A_213, B_214, '#skF_2', '#skF_1', E_215, '#skF_4')=k5_relat_1(E_215, '#skF_4') | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))) | ~v1_funct_1(E_215))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_592])).
% 5.08/1.93  tff(c_1969, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1960])).
% 5.08/1.93  tff(c_1976, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_530, c_1969])).
% 5.08/1.93  tff(c_128, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_119])).
% 5.08/1.93  tff(c_137, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_128])).
% 5.08/1.93  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_157, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_148])).
% 5.08/1.93  tff(c_162, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_157])).
% 5.08/1.93  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_207])).
% 5.08/1.93  tff(c_649, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_643])).
% 5.08/1.93  tff(c_659, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_60, c_649])).
% 5.08/1.93  tff(c_660, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_659])).
% 5.08/1.93  tff(c_668, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_660, c_16])).
% 5.08/1.93  tff(c_680, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_76, c_60, c_81, c_668])).
% 5.08/1.93  tff(c_20, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k1_relat_1(A_12))!=k5_relat_1(A_12, B_14) | k2_relat_1(A_12)!=k1_relat_1(B_14) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.08/1.93  tff(c_77, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_partfun1(k1_relat_1(A_12))!=k5_relat_1(A_12, B_14) | k2_relat_1(A_12)!=k1_relat_1(B_14) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 5.08/1.93  tff(c_686, plain, (![B_14]: (k2_funct_1('#skF_3')=B_14 | k5_relat_1('#skF_3', B_14)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_14) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_680, c_77])).
% 5.08/1.93  tff(c_2026, plain, (![B_220]: (k2_funct_1('#skF_3')=B_220 | k5_relat_1('#skF_3', B_220)!=k6_partfun1('#skF_1') | k1_relat_1(B_220)!='#skF_2' | ~v1_funct_1(B_220) | ~v1_relat_1(B_220))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_76, c_60, c_162, c_686])).
% 5.08/1.93  tff(c_2032, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_134, c_2026])).
% 5.08/1.93  tff(c_2044, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1944, c_1976, c_2032])).
% 5.08/1.93  tff(c_2046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2044])).
% 5.08/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.08/1.93  
% 5.08/1.93  Inference rules
% 5.08/1.93  ----------------------
% 5.08/1.93  #Ref     : 0
% 5.08/1.93  #Sup     : 420
% 5.08/1.93  #Fact    : 0
% 5.08/1.93  #Define  : 0
% 5.08/1.93  #Split   : 15
% 5.08/1.93  #Chain   : 0
% 5.08/1.93  #Close   : 0
% 5.08/1.93  
% 5.08/1.93  Ordering : KBO
% 5.08/1.93  
% 5.08/1.93  Simplification rules
% 5.08/1.93  ----------------------
% 5.08/1.93  #Subsume      : 12
% 5.08/1.93  #Demod        : 505
% 5.08/1.93  #Tautology    : 132
% 5.08/1.93  #SimpNegUnit  : 51
% 5.08/1.93  #BackRed      : 14
% 5.08/1.93  
% 5.08/1.93  #Partial instantiations: 0
% 5.08/1.93  #Strategies tried      : 1
% 5.08/1.93  
% 5.08/1.93  Timing (in seconds)
% 5.08/1.93  ----------------------
% 5.24/1.93  Preprocessing        : 0.39
% 5.24/1.93  Parsing              : 0.21
% 5.24/1.93  CNF conversion       : 0.03
% 5.24/1.93  Main loop            : 0.75
% 5.24/1.93  Inferencing          : 0.25
% 5.24/1.93  Reduction            : 0.28
% 5.25/1.93  Demodulation         : 0.21
% 5.25/1.93  BG Simplification    : 0.04
% 5.25/1.93  Subsumption          : 0.13
% 5.25/1.93  Abstraction          : 0.04
% 5.25/1.93  MUC search           : 0.00
% 5.25/1.93  Cooper               : 0.00
% 5.25/1.93  Total                : 1.19
% 5.25/1.93  Index Insertion      : 0.00
% 5.25/1.93  Index Deletion       : 0.00
% 5.25/1.93  Index Matching       : 0.00
% 5.25/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
