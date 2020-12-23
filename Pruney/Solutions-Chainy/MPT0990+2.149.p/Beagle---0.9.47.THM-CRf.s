%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:18 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 824 expanded)
%              Number of leaves         :   42 ( 310 expanded)
%              Depth                    :   17
%              Number of atoms          :  334 (3494 expanded)
%              Number of equality atoms :  123 (1250 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_193,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_134,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_151,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_167,axiom,(
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

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_98,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_98])).

tff(c_116,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_104,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_98])).

tff(c_113,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_104])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_160,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_171,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_160])).

tff(c_236,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_82,B_81,C_83) = A_82
      | ~ v1_funct_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_242,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_236])).

tff(c_250,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_171,c_242])).

tff(c_251,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_250])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_128,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_134,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_128])).

tff(c_140,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_134])).

tff(c_46,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_649,plain,(
    ! [A_145,B_146] :
      ( k2_funct_1(A_145) = B_146
      | k6_partfun1(k2_relat_1(A_145)) != k5_relat_1(B_146,A_145)
      | k2_relat_1(B_146) != k1_relat_1(A_145)
      | ~ v2_funct_1(A_145)
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_651,plain,(
    ! [B_146] :
      ( k2_funct_1('#skF_3') = B_146
      | k5_relat_1(B_146,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_146) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_649])).

tff(c_654,plain,(
    ! [B_147] :
      ( k2_funct_1('#skF_3') = B_147
      | k5_relat_1(B_147,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_147) != '#skF_1'
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_76,c_60,c_251,c_651])).

tff(c_657,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_116,c_654])).

tff(c_669,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_657])).

tff(c_670,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_669])).

tff(c_676,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_670])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_42,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_117,plain,(
    ! [A_58,B_59,D_60] :
      ( r2_relset_1(A_58,B_59,D_60,D_60)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_124,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_141,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_128])).

tff(c_384,plain,(
    ! [F_112,A_109,B_114,C_111,E_110,D_113] :
      ( k1_partfun1(A_109,B_114,C_111,D_113,E_110,F_112) = k5_relat_1(E_110,F_112)
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_111,D_113)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_114)))
      | ~ v1_funct_1(E_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_390,plain,(
    ! [A_109,B_114,E_110] :
      ( k1_partfun1(A_109,B_114,'#skF_2','#skF_1',E_110,'#skF_4') = k5_relat_1(E_110,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_114)))
      | ~ v1_funct_1(E_110) ) ),
    inference(resolution,[status(thm)],[c_66,c_384])).

tff(c_465,plain,(
    ! [A_123,B_124,E_125] :
      ( k1_partfun1(A_123,B_124,'#skF_2','#skF_1',E_125,'#skF_4') = k5_relat_1(E_125,'#skF_4')
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ v1_funct_1(E_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_390])).

tff(c_471,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_465])).

tff(c_478,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_471])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_281,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_289,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_281])).

tff(c_304,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_289])).

tff(c_305,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_483,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_305])).

tff(c_550,plain,(
    ! [B_140,C_143,A_141,E_144,F_142,D_139] :
      ( m1_subset_1(k1_partfun1(A_141,B_140,C_143,D_139,E_144,F_142),k1_zfmisc_1(k2_zfmisc_1(A_141,D_139)))
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_143,D_139)))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_144,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_1(E_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_607,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_550])).

tff(c_637,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_607])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_483,c_637])).

tff(c_640,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_1370,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( k2_relset_1(A_200,B_201,C_202) = B_201
      | ~ r2_relset_1(B_201,B_201,k1_partfun1(B_201,A_200,A_200,B_201,D_203,C_202),k6_partfun1(B_201))
      | ~ m1_subset_1(D_203,k1_zfmisc_1(k2_zfmisc_1(B_201,A_200)))
      | ~ v1_funct_2(D_203,B_201,A_200)
      | ~ v1_funct_1(D_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_2(C_202,A_200,B_201)
      | ~ v1_funct_1(C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1376,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_1370])).

tff(c_1380,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_124,c_141,c_1376])).

tff(c_1382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_676,c_1380])).

tff(c_1383,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_670])).

tff(c_1384,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_670])).

tff(c_1385,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_141])).

tff(c_172,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_160])).

tff(c_245,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_236])).

tff(c_254,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_172,c_245])).

tff(c_255,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_254])).

tff(c_77,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_partfun1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_1388,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_77])).

tff(c_1392,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k5_relat_1(B_12,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_12) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_70,c_255,c_1388])).

tff(c_1400,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1392])).

tff(c_8,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_1457,plain,(
    ! [B_226,E_222,F_224,A_221,D_225,C_223] :
      ( k1_partfun1(A_221,B_226,C_223,D_225,E_222,F_224) = k5_relat_1(E_222,F_224)
      | ~ m1_subset_1(F_224,k1_zfmisc_1(k2_zfmisc_1(C_223,D_225)))
      | ~ v1_funct_1(F_224)
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_221,B_226)))
      | ~ v1_funct_1(E_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1463,plain,(
    ! [A_221,B_226,E_222] :
      ( k1_partfun1(A_221,B_226,'#skF_2','#skF_1',E_222,'#skF_4') = k5_relat_1(E_222,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_221,B_226)))
      | ~ v1_funct_1(E_222) ) ),
    inference(resolution,[status(thm)],[c_66,c_1457])).

tff(c_1544,plain,(
    ! [A_234,B_235,E_236] :
      ( k1_partfun1(A_234,B_235,'#skF_2','#skF_1',E_236,'#skF_4') = k5_relat_1(E_236,'#skF_4')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1463])).

tff(c_1550,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1544])).

tff(c_1557,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_640,c_1550])).

tff(c_10,plain,(
    ! [A_7,B_9] :
      ( v2_funct_1(A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(k5_relat_1(B_9,A_7))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1567,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1557,c_10])).

tff(c_1573,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_70,c_113,c_76,c_78,c_140,c_255,c_1567])).

tff(c_1575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1400,c_1573])).

tff(c_1577,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1392])).

tff(c_1578,plain,(
    ! [B_237] :
      ( k2_funct_1('#skF_4') = B_237
      | k5_relat_1(B_237,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_237) != '#skF_2'
      | ~ v1_funct_1(B_237)
      | ~ v1_relat_1(B_237) ) ),
    inference(splitRight,[status(thm)],[c_1392])).

tff(c_1584,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_113,c_1578])).

tff(c_1596,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_140,c_1584])).

tff(c_1599,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1596])).

tff(c_1655,plain,(
    ! [A_252,D_256,E_253,B_257,C_254,F_255] :
      ( k1_partfun1(A_252,B_257,C_254,D_256,E_253,F_255) = k5_relat_1(E_253,F_255)
      | ~ m1_subset_1(F_255,k1_zfmisc_1(k2_zfmisc_1(C_254,D_256)))
      | ~ v1_funct_1(F_255)
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_252,B_257)))
      | ~ v1_funct_1(E_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1661,plain,(
    ! [A_252,B_257,E_253] :
      ( k1_partfun1(A_252,B_257,'#skF_2','#skF_1',E_253,'#skF_4') = k5_relat_1(E_253,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_252,B_257)))
      | ~ v1_funct_1(E_253) ) ),
    inference(resolution,[status(thm)],[c_66,c_1655])).

tff(c_1749,plain,(
    ! [A_265,B_266,E_267] :
      ( k1_partfun1(A_265,B_266,'#skF_2','#skF_1',E_267,'#skF_4') = k5_relat_1(E_267,'#skF_4')
      | ~ m1_subset_1(E_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_1(E_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1661])).

tff(c_1755,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1749])).

tff(c_1762,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_640,c_1755])).

tff(c_1764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1599,c_1762])).

tff(c_1765,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1596])).

tff(c_1915,plain,(
    ! [A_294,C_295,B_296] :
      ( k6_partfun1(A_294) = k5_relat_1(C_295,k2_funct_1(C_295))
      | k1_xboole_0 = B_296
      | ~ v2_funct_1(C_295)
      | k2_relset_1(A_294,B_296,C_295) != B_296
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_294,B_296)))
      | ~ v1_funct_2(C_295,A_294,B_296)
      | ~ v1_funct_1(C_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1921,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1915])).

tff(c_1931,plain,
    ( k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1385,c_1577,c_1765,c_1921])).

tff(c_1933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1383,c_1931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.83  
% 4.66/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.84  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.66/1.84  
% 4.66/1.84  %Foreground sorts:
% 4.66/1.84  
% 4.66/1.84  
% 4.66/1.84  %Background operators:
% 4.66/1.84  
% 4.66/1.84  
% 4.66/1.84  %Foreground operators:
% 4.66/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.66/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.66/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.66/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.66/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.66/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/1.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.66/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.66/1.84  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.66/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.66/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.84  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.66/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.66/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.66/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.66/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.66/1.84  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.66/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.66/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.66/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.66/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.66/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.66/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.66/1.84  
% 4.71/1.86  tff(f_193, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.71/1.86  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.71/1.86  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.71/1.86  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.71/1.86  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.71/1.86  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.71/1.86  tff(f_134, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.71/1.86  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.71/1.86  tff(f_122, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.71/1.86  tff(f_88, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.71/1.86  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.71/1.86  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.71/1.86  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.71/1.86  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.71/1.86  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.71/1.86  tff(f_167, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 4.71/1.86  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.71/1.86  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_98, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.71/1.86  tff(c_107, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_98])).
% 4.71/1.86  tff(c_116, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_107])).
% 4.71/1.86  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_104, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_98])).
% 4.71/1.86  tff(c_113, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_104])).
% 4.71/1.86  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_160, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.71/1.86  tff(c_171, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_160])).
% 4.71/1.86  tff(c_236, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_relset_1(A_82, B_81, C_83)=A_82 | ~v1_funct_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.71/1.86  tff(c_242, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_236])).
% 4.71/1.86  tff(c_250, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_171, c_242])).
% 4.71/1.86  tff(c_251, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_250])).
% 4.71/1.86  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_128, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.71/1.86  tff(c_134, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_128])).
% 4.71/1.86  tff(c_140, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_134])).
% 4.71/1.86  tff(c_46, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.71/1.86  tff(c_14, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.71/1.86  tff(c_649, plain, (![A_145, B_146]: (k2_funct_1(A_145)=B_146 | k6_partfun1(k2_relat_1(A_145))!=k5_relat_1(B_146, A_145) | k2_relat_1(B_146)!=k1_relat_1(A_145) | ~v2_funct_1(A_145) | ~v1_funct_1(B_146) | ~v1_relat_1(B_146) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 4.71/1.86  tff(c_651, plain, (![B_146]: (k2_funct_1('#skF_3')=B_146 | k5_relat_1(B_146, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_146)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_146) | ~v1_relat_1(B_146) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_649])).
% 4.71/1.86  tff(c_654, plain, (![B_147]: (k2_funct_1('#skF_3')=B_147 | k5_relat_1(B_147, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_147)!='#skF_1' | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_76, c_60, c_251, c_651])).
% 4.71/1.86  tff(c_657, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_116, c_654])).
% 4.71/1.86  tff(c_669, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_657])).
% 4.71/1.86  tff(c_670, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_669])).
% 4.71/1.86  tff(c_676, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_670])).
% 4.71/1.86  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_42, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.71/1.86  tff(c_117, plain, (![A_58, B_59, D_60]: (r2_relset_1(A_58, B_59, D_60, D_60) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.71/1.86  tff(c_124, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_42, c_117])).
% 4.71/1.86  tff(c_141, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_128])).
% 4.71/1.86  tff(c_384, plain, (![F_112, A_109, B_114, C_111, E_110, D_113]: (k1_partfun1(A_109, B_114, C_111, D_113, E_110, F_112)=k5_relat_1(E_110, F_112) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_111, D_113))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_114))) | ~v1_funct_1(E_110))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.71/1.86  tff(c_390, plain, (![A_109, B_114, E_110]: (k1_partfun1(A_109, B_114, '#skF_2', '#skF_1', E_110, '#skF_4')=k5_relat_1(E_110, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_114))) | ~v1_funct_1(E_110))), inference(resolution, [status(thm)], [c_66, c_384])).
% 4.71/1.86  tff(c_465, plain, (![A_123, B_124, E_125]: (k1_partfun1(A_123, B_124, '#skF_2', '#skF_1', E_125, '#skF_4')=k5_relat_1(E_125, '#skF_4') | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~v1_funct_1(E_125))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_390])).
% 4.71/1.86  tff(c_471, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_465])).
% 4.71/1.86  tff(c_478, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_471])).
% 4.71/1.86  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.71/1.86  tff(c_281, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.71/1.86  tff(c_289, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_281])).
% 4.71/1.86  tff(c_304, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_289])).
% 4.71/1.86  tff(c_305, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_304])).
% 4.71/1.86  tff(c_483, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_305])).
% 4.71/1.86  tff(c_550, plain, (![B_140, C_143, A_141, E_144, F_142, D_139]: (m1_subset_1(k1_partfun1(A_141, B_140, C_143, D_139, E_144, F_142), k1_zfmisc_1(k2_zfmisc_1(A_141, D_139))) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_143, D_139))) | ~v1_funct_1(F_142) | ~m1_subset_1(E_144, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_1(E_144))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.71/1.86  tff(c_607, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_478, c_550])).
% 4.71/1.86  tff(c_637, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_607])).
% 4.71/1.86  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_483, c_637])).
% 4.71/1.86  tff(c_640, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_304])).
% 4.71/1.86  tff(c_1370, plain, (![A_200, B_201, C_202, D_203]: (k2_relset_1(A_200, B_201, C_202)=B_201 | ~r2_relset_1(B_201, B_201, k1_partfun1(B_201, A_200, A_200, B_201, D_203, C_202), k6_partfun1(B_201)) | ~m1_subset_1(D_203, k1_zfmisc_1(k2_zfmisc_1(B_201, A_200))) | ~v1_funct_2(D_203, B_201, A_200) | ~v1_funct_1(D_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_2(C_202, A_200, B_201) | ~v1_funct_1(C_202))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.71/1.86  tff(c_1376, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_640, c_1370])).
% 4.71/1.86  tff(c_1380, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_124, c_141, c_1376])).
% 4.71/1.86  tff(c_1382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_676, c_1380])).
% 4.71/1.86  tff(c_1383, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_670])).
% 4.71/1.86  tff(c_1384, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_670])).
% 4.71/1.86  tff(c_1385, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_141])).
% 4.71/1.86  tff(c_172, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_160])).
% 4.71/1.86  tff(c_245, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_236])).
% 4.71/1.86  tff(c_254, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_172, c_245])).
% 4.71/1.86  tff(c_255, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_254])).
% 4.71/1.86  tff(c_77, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_partfun1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 4.71/1.86  tff(c_1388, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1384, c_77])).
% 4.71/1.86  tff(c_1392, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k5_relat_1(B_12, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_12)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_70, c_255, c_1388])).
% 4.71/1.86  tff(c_1400, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1392])).
% 4.71/1.86  tff(c_8, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.71/1.86  tff(c_78, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 4.71/1.86  tff(c_1457, plain, (![B_226, E_222, F_224, A_221, D_225, C_223]: (k1_partfun1(A_221, B_226, C_223, D_225, E_222, F_224)=k5_relat_1(E_222, F_224) | ~m1_subset_1(F_224, k1_zfmisc_1(k2_zfmisc_1(C_223, D_225))) | ~v1_funct_1(F_224) | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_221, B_226))) | ~v1_funct_1(E_222))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.71/1.86  tff(c_1463, plain, (![A_221, B_226, E_222]: (k1_partfun1(A_221, B_226, '#skF_2', '#skF_1', E_222, '#skF_4')=k5_relat_1(E_222, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_221, B_226))) | ~v1_funct_1(E_222))), inference(resolution, [status(thm)], [c_66, c_1457])).
% 4.71/1.86  tff(c_1544, plain, (![A_234, B_235, E_236]: (k1_partfun1(A_234, B_235, '#skF_2', '#skF_1', E_236, '#skF_4')=k5_relat_1(E_236, '#skF_4') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_236))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1463])).
% 4.71/1.86  tff(c_1550, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1544])).
% 4.71/1.86  tff(c_1557, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_640, c_1550])).
% 4.71/1.86  tff(c_10, plain, (![A_7, B_9]: (v2_funct_1(A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(k5_relat_1(B_9, A_7)) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.71/1.86  tff(c_1567, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1557, c_10])).
% 4.71/1.86  tff(c_1573, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_70, c_113, c_76, c_78, c_140, c_255, c_1567])).
% 4.71/1.86  tff(c_1575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1400, c_1573])).
% 4.71/1.86  tff(c_1577, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1392])).
% 4.71/1.86  tff(c_1578, plain, (![B_237]: (k2_funct_1('#skF_4')=B_237 | k5_relat_1(B_237, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_237)!='#skF_2' | ~v1_funct_1(B_237) | ~v1_relat_1(B_237))), inference(splitRight, [status(thm)], [c_1392])).
% 4.71/1.86  tff(c_1584, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_113, c_1578])).
% 4.71/1.86  tff(c_1596, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_140, c_1584])).
% 4.71/1.86  tff(c_1599, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1596])).
% 4.71/1.86  tff(c_1655, plain, (![A_252, D_256, E_253, B_257, C_254, F_255]: (k1_partfun1(A_252, B_257, C_254, D_256, E_253, F_255)=k5_relat_1(E_253, F_255) | ~m1_subset_1(F_255, k1_zfmisc_1(k2_zfmisc_1(C_254, D_256))) | ~v1_funct_1(F_255) | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_252, B_257))) | ~v1_funct_1(E_253))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.71/1.86  tff(c_1661, plain, (![A_252, B_257, E_253]: (k1_partfun1(A_252, B_257, '#skF_2', '#skF_1', E_253, '#skF_4')=k5_relat_1(E_253, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_252, B_257))) | ~v1_funct_1(E_253))), inference(resolution, [status(thm)], [c_66, c_1655])).
% 4.71/1.86  tff(c_1749, plain, (![A_265, B_266, E_267]: (k1_partfun1(A_265, B_266, '#skF_2', '#skF_1', E_267, '#skF_4')=k5_relat_1(E_267, '#skF_4') | ~m1_subset_1(E_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_1(E_267))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1661])).
% 4.71/1.86  tff(c_1755, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1749])).
% 4.71/1.86  tff(c_1762, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_640, c_1755])).
% 4.71/1.86  tff(c_1764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1599, c_1762])).
% 4.71/1.86  tff(c_1765, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1596])).
% 4.71/1.86  tff(c_1915, plain, (![A_294, C_295, B_296]: (k6_partfun1(A_294)=k5_relat_1(C_295, k2_funct_1(C_295)) | k1_xboole_0=B_296 | ~v2_funct_1(C_295) | k2_relset_1(A_294, B_296, C_295)!=B_296 | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_294, B_296))) | ~v1_funct_2(C_295, A_294, B_296) | ~v1_funct_1(C_295))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.71/1.86  tff(c_1921, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1915])).
% 4.71/1.86  tff(c_1931, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1385, c_1577, c_1765, c_1921])).
% 4.71/1.86  tff(c_1933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1383, c_1931])).
% 4.71/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.86  
% 4.71/1.86  Inference rules
% 4.71/1.86  ----------------------
% 4.71/1.86  #Ref     : 0
% 4.71/1.86  #Sup     : 392
% 4.71/1.86  #Fact    : 0
% 4.71/1.86  #Define  : 0
% 4.71/1.86  #Split   : 20
% 4.71/1.86  #Chain   : 0
% 4.71/1.86  #Close   : 0
% 4.71/1.86  
% 4.71/1.86  Ordering : KBO
% 4.71/1.86  
% 4.71/1.86  Simplification rules
% 4.71/1.86  ----------------------
% 4.71/1.86  #Subsume      : 14
% 4.71/1.86  #Demod        : 425
% 4.71/1.86  #Tautology    : 107
% 4.71/1.86  #SimpNegUnit  : 41
% 4.71/1.86  #BackRed      : 20
% 4.71/1.86  
% 4.71/1.86  #Partial instantiations: 0
% 4.71/1.86  #Strategies tried      : 1
% 4.71/1.86  
% 4.71/1.86  Timing (in seconds)
% 4.71/1.86  ----------------------
% 4.71/1.86  Preprocessing        : 0.39
% 4.71/1.86  Parsing              : 0.21
% 4.71/1.86  CNF conversion       : 0.03
% 4.71/1.86  Main loop            : 0.66
% 4.71/1.86  Inferencing          : 0.23
% 4.71/1.87  Reduction            : 0.24
% 4.71/1.87  Demodulation         : 0.17
% 4.71/1.87  BG Simplification    : 0.03
% 4.71/1.87  Subsumption          : 0.11
% 4.71/1.87  Abstraction          : 0.03
% 4.71/1.87  MUC search           : 0.00
% 4.71/1.87  Cooper               : 0.00
% 4.71/1.87  Total                : 1.10
% 4.71/1.87  Index Insertion      : 0.00
% 4.71/1.87  Index Deletion       : 0.00
% 4.71/1.87  Index Matching       : 0.00
% 4.71/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
