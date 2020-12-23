%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:25 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 386 expanded)
%              Number of leaves         :   41 ( 158 expanded)
%              Depth                    :   12
%              Number of atoms          :  318 (1685 expanded)
%              Number of equality atoms :  110 ( 575 expanded)
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

tff(f_205,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_179,axiom,(
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

tff(f_108,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
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

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_163,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_80,axiom,(
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

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_115,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_124])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_145,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_159,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_145])).

tff(c_637,plain,(
    ! [B_147,C_148,A_149] :
      ( k6_partfun1(B_147) = k5_relat_1(k2_funct_1(C_148),C_148)
      | k1_xboole_0 = B_147
      | ~ v2_funct_1(C_148)
      | k2_relset_1(A_149,B_147,C_148) != B_147
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_147)))
      | ~ v1_funct_2(C_148,A_149,B_147)
      | ~ v1_funct_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_643,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_637])).

tff(c_653,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_159,c_643])).

tff(c_654,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_653])).

tff(c_659,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_32,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_135,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_142,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_286,plain,(
    ! [E_99,D_95,B_96,C_100,F_98,A_97] :
      ( k1_partfun1(A_97,B_96,C_100,D_95,E_99,F_98) = k5_relat_1(E_99,F_98)
      | ~ m1_subset_1(F_98,k1_zfmisc_1(k2_zfmisc_1(C_100,D_95)))
      | ~ v1_funct_1(F_98)
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_1(E_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_292,plain,(
    ! [A_97,B_96,E_99] :
      ( k1_partfun1(A_97,B_96,'#skF_2','#skF_1',E_99,'#skF_4') = k5_relat_1(E_99,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_1(E_99) ) ),
    inference(resolution,[status(thm)],[c_64,c_286])).

tff(c_352,plain,(
    ! [A_109,B_110,E_111] :
      ( k1_partfun1(A_109,B_110,'#skF_2','#skF_1',E_111,'#skF_4') = k5_relat_1(E_111,'#skF_4')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_292])).

tff(c_358,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_352])).

tff(c_365,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_358])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_203,plain,(
    ! [D_74,C_75,A_76,B_77] :
      ( D_74 = C_75
      | ~ r2_relset_1(A_76,B_77,C_75,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_211,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_203])).

tff(c_226,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_211])).

tff(c_236,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_370,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_236])).

tff(c_465,plain,(
    ! [B_122,E_119,F_120,A_117,D_121,C_118] :
      ( m1_subset_1(k1_partfun1(A_117,B_122,C_118,D_121,E_119,F_120),k1_zfmisc_1(k2_zfmisc_1(A_117,D_121)))
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_118,D_121)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_122)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_499,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_465])).

tff(c_522,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_499])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_522])).

tff(c_525,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_1350,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_relset_1(A_182,B_183,C_184) = B_183
      | ~ r2_relset_1(B_183,B_183,k1_partfun1(B_183,A_182,A_182,B_183,D_185,C_184),k6_partfun1(B_183))
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(B_183,A_182)))
      | ~ v1_funct_2(D_185,B_183,A_182)
      | ~ v1_funct_1(D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(C_184,A_182,B_183)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1359,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_1350])).

tff(c_1366,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_142,c_159,c_1359])).

tff(c_1368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_659,c_1366])).

tff(c_1369,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_1380,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1369])).

tff(c_36,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_10,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1931,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1937,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_525,c_1931])).

tff(c_1945,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_77,c_62,c_1937])).

tff(c_1947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1380,c_56,c_1945])).

tff(c_1949,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1369])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_1370,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_1371,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1370,c_159])).

tff(c_1994,plain,(
    ! [A_217,C_218,B_219] :
      ( k6_partfun1(A_217) = k5_relat_1(C_218,k2_funct_1(C_218))
      | k1_xboole_0 = B_219
      | ~ v2_funct_1(C_218)
      | k2_relset_1(A_217,B_219,C_218) != B_219
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_217,B_219)))
      | ~ v1_funct_2(C_218,A_217,B_219)
      | ~ v1_funct_1(C_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2000,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1994])).

tff(c_2010,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1371,c_1949,c_2000])).

tff(c_2011,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2010])).

tff(c_14,plain,(
    ! [A_11] :
      ( k2_relat_1(k5_relat_1(A_11,k2_funct_1(A_11))) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2057,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2011,c_14])).

tff(c_2068,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_68,c_1949,c_78,c_2057])).

tff(c_583,plain,(
    ! [E_140,B_137,A_138,C_141,F_139,D_136] :
      ( k1_partfun1(A_138,B_137,C_141,D_136,E_140,F_139) = k5_relat_1(E_140,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_141,D_136)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_589,plain,(
    ! [A_138,B_137,E_140] :
      ( k1_partfun1(A_138,B_137,'#skF_2','#skF_1',E_140,'#skF_4') = k5_relat_1(E_140,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_140) ) ),
    inference(resolution,[status(thm)],[c_64,c_583])).

tff(c_598,plain,(
    ! [A_143,B_144,E_145] :
      ( k1_partfun1(A_143,B_144,'#skF_2','#skF_1',E_145,'#skF_4') = k5_relat_1(E_145,'#skF_4')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_589])).

tff(c_604,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_598])).

tff(c_611,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_525,c_604])).

tff(c_121,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_115])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_151,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_145])).

tff(c_158,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_151])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1998,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1994])).

tff(c_2006,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_1998])).

tff(c_2007,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2006])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_relat_1(k5_relat_1(A_11,k2_funct_1(A_11))) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2019,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2007,c_16])).

tff(c_2031,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_74,c_58,c_79,c_2019])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k1_relat_1(A_12)) != k5_relat_1(A_12,B_14)
      | k2_relat_1(A_12) != k1_relat_1(B_14)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_75,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_partfun1(k1_relat_1(A_12)) != k5_relat_1(A_12,B_14)
      | k2_relat_1(A_12) != k1_relat_1(B_14)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18])).

tff(c_2037,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_3') = B_14
      | k5_relat_1('#skF_3',B_14) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_14)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2031,c_75])).

tff(c_2084,plain,(
    ! [B_220] :
      ( k2_funct_1('#skF_3') = B_220
      | k5_relat_1('#skF_3',B_220) != k6_partfun1('#skF_1')
      | k1_relat_1(B_220) != '#skF_2'
      | ~ v1_funct_1(B_220)
      | ~ v1_relat_1(B_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_74,c_58,c_158,c_2037])).

tff(c_2090,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_2084])).

tff(c_2101,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2068,c_611,c_2090])).

tff(c_2103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.80  
% 4.45/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.80  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.45/1.80  
% 4.45/1.80  %Foreground sorts:
% 4.45/1.80  
% 4.45/1.80  
% 4.45/1.80  %Background operators:
% 4.45/1.80  
% 4.45/1.80  
% 4.45/1.80  %Foreground operators:
% 4.45/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.45/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.45/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.45/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.80  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.45/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.80  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.45/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.45/1.80  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.45/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.80  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.45/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.80  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.45/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.45/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.80  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.45/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.45/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.80  
% 4.73/1.82  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.73/1.82  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.73/1.82  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.73/1.82  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.73/1.82  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 4.73/1.82  tff(f_108, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.73/1.82  tff(f_92, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.73/1.82  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.73/1.82  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.73/1.82  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.73/1.82  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.73/1.82  tff(f_40, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 4.73/1.82  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 4.73/1.82  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.73/1.82  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 4.73/1.82  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.73/1.82  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.73/1.82  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_115, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.73/1.82  tff(c_124, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_115])).
% 4.73/1.82  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_124])).
% 4.73/1.82  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_145, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.73/1.82  tff(c_159, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_145])).
% 4.73/1.82  tff(c_637, plain, (![B_147, C_148, A_149]: (k6_partfun1(B_147)=k5_relat_1(k2_funct_1(C_148), C_148) | k1_xboole_0=B_147 | ~v2_funct_1(C_148) | k2_relset_1(A_149, B_147, C_148)!=B_147 | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_147))) | ~v1_funct_2(C_148, A_149, B_147) | ~v1_funct_1(C_148))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.73/1.82  tff(c_643, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_637])).
% 4.73/1.82  tff(c_653, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_159, c_643])).
% 4.73/1.82  tff(c_654, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_653])).
% 4.73/1.82  tff(c_659, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_654])).
% 4.73/1.82  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_32, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.73/1.82  tff(c_135, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.73/1.82  tff(c_142, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_32, c_135])).
% 4.73/1.82  tff(c_286, plain, (![E_99, D_95, B_96, C_100, F_98, A_97]: (k1_partfun1(A_97, B_96, C_100, D_95, E_99, F_98)=k5_relat_1(E_99, F_98) | ~m1_subset_1(F_98, k1_zfmisc_1(k2_zfmisc_1(C_100, D_95))) | ~v1_funct_1(F_98) | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_1(E_99))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_292, plain, (![A_97, B_96, E_99]: (k1_partfun1(A_97, B_96, '#skF_2', '#skF_1', E_99, '#skF_4')=k5_relat_1(E_99, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_1(E_99))), inference(resolution, [status(thm)], [c_64, c_286])).
% 4.73/1.82  tff(c_352, plain, (![A_109, B_110, E_111]: (k1_partfun1(A_109, B_110, '#skF_2', '#skF_1', E_111, '#skF_4')=k5_relat_1(E_111, '#skF_4') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_1(E_111))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_292])).
% 4.73/1.82  tff(c_358, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_352])).
% 4.73/1.82  tff(c_365, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_358])).
% 4.73/1.82  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_203, plain, (![D_74, C_75, A_76, B_77]: (D_74=C_75 | ~r2_relset_1(A_76, B_77, C_75, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.73/1.82  tff(c_211, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_203])).
% 4.73/1.82  tff(c_226, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_211])).
% 4.73/1.82  tff(c_236, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_226])).
% 4.73/1.82  tff(c_370, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_236])).
% 4.73/1.82  tff(c_465, plain, (![B_122, E_119, F_120, A_117, D_121, C_118]: (m1_subset_1(k1_partfun1(A_117, B_122, C_118, D_121, E_119, F_120), k1_zfmisc_1(k2_zfmisc_1(A_117, D_121))) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_118, D_121))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_122))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.73/1.82  tff(c_499, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_365, c_465])).
% 4.73/1.82  tff(c_522, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_499])).
% 4.73/1.82  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_522])).
% 4.73/1.82  tff(c_525, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_226])).
% 4.73/1.82  tff(c_1350, plain, (![A_182, B_183, C_184, D_185]: (k2_relset_1(A_182, B_183, C_184)=B_183 | ~r2_relset_1(B_183, B_183, k1_partfun1(B_183, A_182, A_182, B_183, D_185, C_184), k6_partfun1(B_183)) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(B_183, A_182))) | ~v1_funct_2(D_185, B_183, A_182) | ~v1_funct_1(D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(C_184, A_182, B_183) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.73/1.82  tff(c_1359, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_525, c_1350])).
% 4.73/1.82  tff(c_1366, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_142, c_159, c_1359])).
% 4.73/1.82  tff(c_1368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_659, c_1366])).
% 4.73/1.82  tff(c_1369, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_654])).
% 4.73/1.82  tff(c_1380, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1369])).
% 4.73/1.82  tff(c_36, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.73/1.82  tff(c_10, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.73/1.82  tff(c_77, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 4.73/1.82  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_1931, plain, (![B_212, A_209, C_210, D_211, E_208]: (k1_xboole_0=C_210 | v2_funct_1(E_208) | k2_relset_1(A_209, B_212, D_211)!=B_212 | ~v2_funct_1(k1_partfun1(A_209, B_212, B_212, C_210, D_211, E_208)) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(B_212, C_210))) | ~v1_funct_2(E_208, B_212, C_210) | ~v1_funct_1(E_208) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_212))) | ~v1_funct_2(D_211, A_209, B_212) | ~v1_funct_1(D_211))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.73/1.82  tff(c_1937, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_525, c_1931])).
% 4.73/1.82  tff(c_1945, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_77, c_62, c_1937])).
% 4.73/1.82  tff(c_1947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1380, c_56, c_1945])).
% 4.73/1.82  tff(c_1949, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1369])).
% 4.73/1.82  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.73/1.82  tff(c_78, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 4.73/1.82  tff(c_1370, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_654])).
% 4.73/1.82  tff(c_1371, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1370, c_159])).
% 4.73/1.82  tff(c_1994, plain, (![A_217, C_218, B_219]: (k6_partfun1(A_217)=k5_relat_1(C_218, k2_funct_1(C_218)) | k1_xboole_0=B_219 | ~v2_funct_1(C_218) | k2_relset_1(A_217, B_219, C_218)!=B_219 | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_217, B_219))) | ~v1_funct_2(C_218, A_217, B_219) | ~v1_funct_1(C_218))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.73/1.82  tff(c_2000, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1994])).
% 4.73/1.82  tff(c_2010, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1371, c_1949, c_2000])).
% 4.73/1.82  tff(c_2011, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_2010])).
% 4.73/1.82  tff(c_14, plain, (![A_11]: (k2_relat_1(k5_relat_1(A_11, k2_funct_1(A_11)))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.73/1.82  tff(c_2057, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2011, c_14])).
% 4.73/1.82  tff(c_2068, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_68, c_1949, c_78, c_2057])).
% 4.73/1.82  tff(c_583, plain, (![E_140, B_137, A_138, C_141, F_139, D_136]: (k1_partfun1(A_138, B_137, C_141, D_136, E_140, F_139)=k5_relat_1(E_140, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_141, D_136))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.73/1.82  tff(c_589, plain, (![A_138, B_137, E_140]: (k1_partfun1(A_138, B_137, '#skF_2', '#skF_1', E_140, '#skF_4')=k5_relat_1(E_140, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_140))), inference(resolution, [status(thm)], [c_64, c_583])).
% 4.73/1.82  tff(c_598, plain, (![A_143, B_144, E_145]: (k1_partfun1(A_143, B_144, '#skF_2', '#skF_1', E_145, '#skF_4')=k5_relat_1(E_145, '#skF_4') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_1(E_145))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_589])).
% 4.73/1.82  tff(c_604, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_598])).
% 4.73/1.82  tff(c_611, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_525, c_604])).
% 4.73/1.82  tff(c_121, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_115])).
% 4.73/1.82  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_121])).
% 4.73/1.82  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_151, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_145])).
% 4.73/1.82  tff(c_158, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_151])).
% 4.73/1.82  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.73/1.82  tff(c_79, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 4.73/1.82  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.73/1.82  tff(c_1998, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1994])).
% 4.73/1.82  tff(c_2006, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_1998])).
% 4.73/1.82  tff(c_2007, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_2006])).
% 4.73/1.82  tff(c_16, plain, (![A_11]: (k1_relat_1(k5_relat_1(A_11, k2_funct_1(A_11)))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.73/1.82  tff(c_2019, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2007, c_16])).
% 4.73/1.82  tff(c_2031, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_74, c_58, c_79, c_2019])).
% 4.73/1.82  tff(c_18, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k1_relat_1(A_12))!=k5_relat_1(A_12, B_14) | k2_relat_1(A_12)!=k1_relat_1(B_14) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.73/1.82  tff(c_75, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_partfun1(k1_relat_1(A_12))!=k5_relat_1(A_12, B_14) | k2_relat_1(A_12)!=k1_relat_1(B_14) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18])).
% 4.73/1.82  tff(c_2037, plain, (![B_14]: (k2_funct_1('#skF_3')=B_14 | k5_relat_1('#skF_3', B_14)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_14) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2031, c_75])).
% 4.73/1.82  tff(c_2084, plain, (![B_220]: (k2_funct_1('#skF_3')=B_220 | k5_relat_1('#skF_3', B_220)!=k6_partfun1('#skF_1') | k1_relat_1(B_220)!='#skF_2' | ~v1_funct_1(B_220) | ~v1_relat_1(B_220))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_74, c_58, c_158, c_2037])).
% 4.73/1.82  tff(c_2090, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_2084])).
% 4.73/1.82  tff(c_2101, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2068, c_611, c_2090])).
% 4.73/1.82  tff(c_2103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2101])).
% 4.73/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.82  
% 4.73/1.82  Inference rules
% 4.73/1.82  ----------------------
% 4.73/1.82  #Ref     : 0
% 4.73/1.83  #Sup     : 436
% 4.73/1.83  #Fact    : 0
% 4.73/1.83  #Define  : 0
% 4.73/1.83  #Split   : 12
% 4.73/1.83  #Chain   : 0
% 4.73/1.83  #Close   : 0
% 4.73/1.83  
% 4.73/1.83  Ordering : KBO
% 4.73/1.83  
% 4.73/1.83  Simplification rules
% 4.73/1.83  ----------------------
% 4.73/1.83  #Subsume      : 12
% 4.73/1.83  #Demod        : 551
% 4.73/1.83  #Tautology    : 142
% 4.73/1.83  #SimpNegUnit  : 52
% 4.73/1.83  #BackRed      : 16
% 4.73/1.83  
% 4.73/1.83  #Partial instantiations: 0
% 4.73/1.83  #Strategies tried      : 1
% 4.73/1.83  
% 4.73/1.83  Timing (in seconds)
% 4.73/1.83  ----------------------
% 4.73/1.83  Preprocessing        : 0.37
% 4.73/1.83  Parsing              : 0.19
% 4.73/1.83  CNF conversion       : 0.03
% 4.73/1.83  Main loop            : 0.68
% 4.73/1.83  Inferencing          : 0.22
% 4.73/1.83  Reduction            : 0.27
% 4.73/1.83  Demodulation         : 0.19
% 4.73/1.83  BG Simplification    : 0.03
% 4.73/1.83  Subsumption          : 0.12
% 4.73/1.83  Abstraction          : 0.03
% 4.73/1.83  MUC search           : 0.00
% 4.73/1.83  Cooper               : 0.00
% 4.73/1.83  Total                : 1.09
% 4.73/1.83  Index Insertion      : 0.00
% 4.73/1.83  Index Deletion       : 0.00
% 4.73/1.83  Index Matching       : 0.00
% 4.73/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
