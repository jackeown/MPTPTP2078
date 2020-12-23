%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:26 EST 2020

% Result     : Theorem 13.17s
% Output     : CNFRefutation 13.39s
% Verified   : 
% Statistics : Number of formulae       :  180 (1579 expanded)
%              Number of leaves         :   41 ( 576 expanded)
%              Depth                    :   24
%              Number of atoms          :  461 (6285 expanded)
%              Number of equality atoms :  176 (2259 expanded)
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

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

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

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

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

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_365,plain,(
    ! [B_98,C_102,A_99,D_97,F_100,E_101] :
      ( k1_partfun1(A_99,B_98,C_102,D_97,E_101,F_100) = k5_relat_1(E_101,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_102,D_97)))
      | ~ v1_funct_1(F_100)
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_1(E_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_371,plain,(
    ! [A_99,B_98,E_101] :
      ( k1_partfun1(A_99,B_98,'#skF_2','#skF_1',E_101,'#skF_4') = k5_relat_1(E_101,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_1(E_101) ) ),
    inference(resolution,[status(thm)],[c_62,c_365])).

tff(c_583,plain,(
    ! [A_115,B_116,E_117] :
      ( k1_partfun1(A_115,B_116,'#skF_2','#skF_1',E_117,'#skF_4') = k5_relat_1(E_117,'#skF_4')
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(E_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_371])).

tff(c_589,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_583])).

tff(c_596,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_589])).

tff(c_34,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_26,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_73,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_237,plain,(
    ! [D_75,C_76,A_77,B_78] :
      ( D_75 = C_76
      | ~ r2_relset_1(A_77,B_78,C_76,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_245,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_237])).

tff(c_260,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_245])).

tff(c_261,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_605,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_261])).

tff(c_611,plain,(
    ! [D_122,B_121,A_123,F_119,E_120,C_118] :
      ( m1_subset_1(k1_partfun1(A_123,B_121,C_118,D_122,E_120,F_119),k1_zfmisc_1(k2_zfmisc_1(A_123,D_122)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_118,D_122)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_123,B_121)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_642,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_611])).

tff(c_663,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_642])).

tff(c_683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_663])).

tff(c_684,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_716,plain,(
    ! [C_126,D_130,B_129,F_127,A_131,E_128] :
      ( v1_funct_1(k1_partfun1(A_131,B_129,C_126,D_130,E_128,F_127))
      | ~ m1_subset_1(F_127,k1_zfmisc_1(k2_zfmisc_1(C_126,D_130)))
      | ~ v1_funct_1(F_127)
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_131,B_129)))
      | ~ v1_funct_1(E_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_722,plain,(
    ! [A_131,B_129,E_128] :
      ( v1_funct_1(k1_partfun1(A_131,B_129,'#skF_2','#skF_1',E_128,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_131,B_129)))
      | ~ v1_funct_1(E_128) ) ),
    inference(resolution,[status(thm)],[c_62,c_716])).

tff(c_754,plain,(
    ! [A_138,B_139,E_140] :
      ( v1_funct_1(k1_partfun1(A_138,B_139,'#skF_2','#skF_1',E_140,'#skF_4'))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_722])).

tff(c_760,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_754])).

tff(c_767,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_684,c_760])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_114,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [A_22] :
      ( v1_relat_1(k6_partfun1(A_22))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,A_22)) ) ),
    inference(resolution,[status(thm)],[c_73,c_114])).

tff(c_126,plain,(
    ! [A_22] : v1_relat_1(k6_partfun1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_117])).

tff(c_120,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_114])).

tff(c_129,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_120])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_167,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_173,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_167])).

tff(c_180,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_173])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k2_relat_1(A_12)) != k5_relat_1(B_14,A_12)
      | k2_relat_1(B_14) != k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_693,plain,(
    ! [A_124,B_125] :
      ( k2_funct_1(A_124) = B_125
      | k6_partfun1(k2_relat_1(A_124)) != k5_relat_1(B_125,A_124)
      | k2_relat_1(B_125) != k1_relat_1(A_124)
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_699,plain,(
    ! [B_125] :
      ( k2_funct_1('#skF_3') = B_125
      | k5_relat_1(B_125,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_125) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_693])).

tff(c_804,plain,(
    ! [B_148] :
      ( k2_funct_1('#skF_3') = B_148
      | k5_relat_1(B_148,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_148) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_699])).

tff(c_807,plain,(
    ! [A_22] :
      ( k6_partfun1(A_22) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_22),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_22)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_126,c_804])).

tff(c_830,plain,(
    ! [A_149] :
      ( k6_partfun1(A_149) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_149),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_149
      | ~ v1_funct_1(k6_partfun1(A_149)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_807])).

tff(c_834,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_767,c_830])).

tff(c_835,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_834])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_901,plain,(
    ! [A_156,C_157,B_158] :
      ( k6_partfun1(A_156) = k5_relat_1(C_157,k2_funct_1(C_157))
      | k1_xboole_0 = B_158
      | ~ v2_funct_1(C_157)
      | k2_relset_1(A_156,B_158,C_157) != B_158
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_158)))
      | ~ v1_funct_2(C_157,A_156,B_158)
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_905,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_901])).

tff(c_913,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_905])).

tff(c_914,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_913])).

tff(c_16,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_75,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_partfun1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_924,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_75])).

tff(c_933,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_924])).

tff(c_980,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_80])).

tff(c_1006,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_980])).

tff(c_1008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_835,c_1006])).

tff(c_1010,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_123,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_810,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_804])).

tff(c_821,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_810])).

tff(c_822,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_821])).

tff(c_827,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_822])).

tff(c_1013,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_827])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_157,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_164,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_73,c_157])).

tff(c_181,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_167])).

tff(c_1589,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k2_relset_1(A_189,B_190,C_191) = B_190
      | ~ r2_relset_1(B_190,B_190,k1_partfun1(B_190,A_189,A_189,B_190,D_192,C_191),k6_partfun1(B_190))
      | ~ m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1(B_190,A_189)))
      | ~ v1_funct_2(D_192,B_190,A_189)
      | ~ v1_funct_1(D_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_2(C_191,A_189,B_190)
      | ~ v1_funct_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1595,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_1589])).

tff(c_1599,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_164,c_181,c_1595])).

tff(c_1601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1013,c_1599])).

tff(c_1602,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_822])).

tff(c_789,plain,(
    ! [D_141,A_143,E_145,B_142,F_144,C_146] :
      ( k1_partfun1(A_143,B_142,C_146,D_141,E_145,F_144) = k5_relat_1(E_145,F_144)
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(C_146,D_141)))
      | ~ v1_funct_1(F_144)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_795,plain,(
    ! [A_143,B_142,E_145] :
      ( k1_partfun1(A_143,B_142,'#skF_2','#skF_1',E_145,'#skF_4') = k5_relat_1(E_145,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142)))
      | ~ v1_funct_1(E_145) ) ),
    inference(resolution,[status(thm)],[c_62,c_789])).

tff(c_1617,plain,(
    ! [A_193,B_194,E_195] :
      ( k1_partfun1(A_193,B_194,'#skF_2','#skF_1',E_195,'#skF_4') = k5_relat_1(E_195,'#skF_4')
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_795])).

tff(c_1623,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1617])).

tff(c_1630,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_684,c_1623])).

tff(c_1644,plain,(
    ! [A_196,C_197,B_198] :
      ( k6_partfun1(A_196) = k5_relat_1(C_197,k2_funct_1(C_197))
      | k1_xboole_0 = B_198
      | ~ v2_funct_1(C_197)
      | k2_relset_1(A_196,B_198,C_197) != B_198
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_198)))
      | ~ v1_funct_2(C_197,A_196,B_198)
      | ~ v1_funct_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1648,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1644])).

tff(c_1656,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_1648])).

tff(c_1657,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1656])).

tff(c_1667,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_75])).

tff(c_1676,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_1667])).

tff(c_1720,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_80])).

tff(c_1743,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1720])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1603,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_822])).

tff(c_1604,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1603,c_181])).

tff(c_1778,plain,(
    ! [B_199,C_200,A_201] :
      ( k6_partfun1(B_199) = k5_relat_1(k2_funct_1(C_200),C_200)
      | k1_xboole_0 = B_199
      | ~ v2_funct_1(C_200)
      | k2_relset_1(A_201,B_199,C_200) != B_199
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_199)))
      | ~ v1_funct_2(C_200,A_201,B_199)
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1784,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1778])).

tff(c_1794,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1604,c_1784])).

tff(c_1795,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1794])).

tff(c_1907,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1743,c_1795])).

tff(c_1908,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1907])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_7)),A_7) = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,(
    ! [A_60] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_60)),A_60) = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_143,plain,(
    ! [A_6] :
      ( k5_relat_1(k6_partfun1(A_6),k6_partfun1(A_6)) = k6_partfun1(A_6)
      | ~ v1_relat_1(k6_partfun1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_134])).

tff(c_147,plain,(
    ! [A_6] : k5_relat_1(k6_partfun1(A_6),k6_partfun1(A_6)) = k6_partfun1(A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_143])).

tff(c_12,plain,(
    ! [A_8,B_10] :
      ( v2_funct_1(A_8)
      | k6_relat_1(k1_relat_1(A_8)) != k5_relat_1(A_8,B_10)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_218,plain,(
    ! [A_72,B_73] :
      ( v2_funct_1(A_72)
      | k6_partfun1(k1_relat_1(A_72)) != k5_relat_1(A_72,B_73)
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73)
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_224,plain,(
    ! [A_6] :
      ( v2_funct_1(k6_partfun1(A_6))
      | k6_partfun1(k1_relat_1(k6_partfun1(A_6))) != k6_partfun1(A_6)
      | ~ v1_funct_1(k6_partfun1(A_6))
      | ~ v1_relat_1(k6_partfun1(A_6))
      | ~ v1_funct_1(k6_partfun1(A_6))
      | ~ v1_relat_1(k6_partfun1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_218])).

tff(c_231,plain,(
    ! [A_6] :
      ( v2_funct_1(k6_partfun1(A_6))
      | ~ v1_funct_1(k6_partfun1(A_6)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_126,c_80,c_224])).

tff(c_1692,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1(k6_partfun1(k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_231])).

tff(c_1733,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_1676,c_1692])).

tff(c_2045,plain,(
    ! [E_216,A_217,B_220,D_219,C_218] :
      ( k1_xboole_0 = C_218
      | v2_funct_1(E_216)
      | k2_relset_1(A_217,B_220,D_219) != B_220
      | ~ v2_funct_1(k1_partfun1(A_217,B_220,B_220,C_218,D_219,E_216))
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(B_220,C_218)))
      | ~ v1_funct_2(E_216,B_220,C_218)
      | ~ v1_funct_1(E_216)
      | ~ m1_subset_1(D_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_220)))
      | ~ v1_funct_2(D_219,A_217,B_220)
      | ~ v1_funct_1(D_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2047,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_684,c_2045])).

tff(c_2049,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_1733,c_60,c_2047])).

tff(c_2051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1908,c_54,c_2049])).

tff(c_2053,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1907])).

tff(c_1650,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1644])).

tff(c_1660,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1604,c_1650])).

tff(c_1661,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1660])).

tff(c_1746,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1661])).

tff(c_1775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1743,c_1746])).

tff(c_1776,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1661])).

tff(c_2128,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_1776])).

tff(c_2134,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_75])).

tff(c_2143,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_66,c_2053,c_2134])).

tff(c_2187,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2143,c_80])).

tff(c_2206,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2187])).

tff(c_1799,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1743,c_1603])).

tff(c_74,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_partfun1(k2_relat_1(A_12)) != k5_relat_1(B_14,A_12)
      | k2_relat_1(B_14) != k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_1836,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_4') = B_14
      | k5_relat_1(B_14,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_14) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1799,c_74])).

tff(c_1840,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_4') = B_14
      | k5_relat_1(B_14,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_14) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_66,c_1836])).

tff(c_13100,plain,(
    ! [B_540] :
      ( k2_funct_1('#skF_4') = B_540
      | k5_relat_1(B_540,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_540) != '#skF_2'
      | ~ v1_funct_1(B_540)
      | ~ v1_relat_1(B_540) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2053,c_2206,c_1840])).

tff(c_13427,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_13100])).

tff(c_13646,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_180,c_1630,c_13427])).

tff(c_13649,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13646,c_2128])).

tff(c_13652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1602,c_13649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.17/5.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.17/5.99  
% 13.17/5.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.17/5.99  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.17/5.99  
% 13.17/5.99  %Foreground sorts:
% 13.17/5.99  
% 13.17/5.99  
% 13.17/5.99  %Background operators:
% 13.17/5.99  
% 13.17/5.99  
% 13.17/5.99  %Foreground operators:
% 13.17/5.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.17/5.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.17/5.99  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.17/5.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.17/5.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.17/5.99  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.17/5.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.17/5.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.17/5.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.17/5.99  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.17/5.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.17/5.99  tff('#skF_2', type, '#skF_2': $i).
% 13.17/5.99  tff('#skF_3', type, '#skF_3': $i).
% 13.17/5.99  tff('#skF_1', type, '#skF_1': $i).
% 13.17/5.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.17/5.99  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.17/5.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.17/5.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.17/5.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.17/5.99  tff('#skF_4', type, '#skF_4': $i).
% 13.17/5.99  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.17/5.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.17/5.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.17/5.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.17/5.99  
% 13.39/6.02  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 13.39/6.02  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.39/6.02  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.39/6.02  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 13.39/6.02  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.39/6.02  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.39/6.02  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 13.39/6.02  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.39/6.02  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.39/6.02  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.39/6.02  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 13.39/6.02  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 13.39/6.02  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 13.39/6.02  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 13.39/6.02  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 13.39/6.02  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 13.39/6.02  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 13.39/6.02  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_365, plain, (![B_98, C_102, A_99, D_97, F_100, E_101]: (k1_partfun1(A_99, B_98, C_102, D_97, E_101, F_100)=k5_relat_1(E_101, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_102, D_97))) | ~v1_funct_1(F_100) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_1(E_101))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.39/6.02  tff(c_371, plain, (![A_99, B_98, E_101]: (k1_partfun1(A_99, B_98, '#skF_2', '#skF_1', E_101, '#skF_4')=k5_relat_1(E_101, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_1(E_101))), inference(resolution, [status(thm)], [c_62, c_365])).
% 13.39/6.02  tff(c_583, plain, (![A_115, B_116, E_117]: (k1_partfun1(A_115, B_116, '#skF_2', '#skF_1', E_117, '#skF_4')=k5_relat_1(E_117, '#skF_4') | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(E_117))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_371])).
% 13.39/6.02  tff(c_589, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_583])).
% 13.39/6.02  tff(c_596, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_589])).
% 13.39/6.02  tff(c_34, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.39/6.02  tff(c_26, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.39/6.02  tff(c_73, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26])).
% 13.39/6.02  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_237, plain, (![D_75, C_76, A_77, B_78]: (D_75=C_76 | ~r2_relset_1(A_77, B_78, C_76, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.39/6.02  tff(c_245, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_237])).
% 13.39/6.02  tff(c_260, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_245])).
% 13.39/6.02  tff(c_261, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_260])).
% 13.39/6.02  tff(c_605, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_596, c_261])).
% 13.39/6.02  tff(c_611, plain, (![D_122, B_121, A_123, F_119, E_120, C_118]: (m1_subset_1(k1_partfun1(A_123, B_121, C_118, D_122, E_120, F_119), k1_zfmisc_1(k2_zfmisc_1(A_123, D_122))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_118, D_122))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_123, B_121))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.39/6.02  tff(c_642, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_596, c_611])).
% 13.39/6.02  tff(c_663, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_642])).
% 13.39/6.02  tff(c_683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_605, c_663])).
% 13.39/6.02  tff(c_684, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_260])).
% 13.39/6.02  tff(c_716, plain, (![C_126, D_130, B_129, F_127, A_131, E_128]: (v1_funct_1(k1_partfun1(A_131, B_129, C_126, D_130, E_128, F_127)) | ~m1_subset_1(F_127, k1_zfmisc_1(k2_zfmisc_1(C_126, D_130))) | ~v1_funct_1(F_127) | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_131, B_129))) | ~v1_funct_1(E_128))), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.39/6.02  tff(c_722, plain, (![A_131, B_129, E_128]: (v1_funct_1(k1_partfun1(A_131, B_129, '#skF_2', '#skF_1', E_128, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_131, B_129))) | ~v1_funct_1(E_128))), inference(resolution, [status(thm)], [c_62, c_716])).
% 13.39/6.02  tff(c_754, plain, (![A_138, B_139, E_140]: (v1_funct_1(k1_partfun1(A_138, B_139, '#skF_2', '#skF_1', E_140, '#skF_4')) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_722])).
% 13.39/6.02  tff(c_760, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_754])).
% 13.39/6.02  tff(c_767, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_684, c_760])).
% 13.39/6.02  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.39/6.02  tff(c_79, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 13.39/6.02  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.39/6.02  tff(c_114, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.39/6.02  tff(c_117, plain, (![A_22]: (v1_relat_1(k6_partfun1(A_22)) | ~v1_relat_1(k2_zfmisc_1(A_22, A_22)))), inference(resolution, [status(thm)], [c_73, c_114])).
% 13.39/6.02  tff(c_126, plain, (![A_22]: (v1_relat_1(k6_partfun1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_117])).
% 13.39/6.02  tff(c_120, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_114])).
% 13.39/6.02  tff(c_129, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_120])).
% 13.39/6.02  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_167, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.39/6.02  tff(c_173, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_167])).
% 13.39/6.02  tff(c_180, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_173])).
% 13.39/6.02  tff(c_18, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k2_relat_1(A_12))!=k5_relat_1(B_14, A_12) | k2_relat_1(B_14)!=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.39/6.02  tff(c_693, plain, (![A_124, B_125]: (k2_funct_1(A_124)=B_125 | k6_partfun1(k2_relat_1(A_124))!=k5_relat_1(B_125, A_124) | k2_relat_1(B_125)!=k1_relat_1(A_124) | ~v2_funct_1(A_124) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 13.39/6.02  tff(c_699, plain, (![B_125]: (k2_funct_1('#skF_3')=B_125 | k5_relat_1(B_125, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_125)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_693])).
% 13.39/6.02  tff(c_804, plain, (![B_148]: (k2_funct_1('#skF_3')=B_148 | k5_relat_1(B_148, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_148)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_699])).
% 13.39/6.02  tff(c_807, plain, (![A_22]: (k6_partfun1(A_22)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_22), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_22))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_126, c_804])).
% 13.39/6.02  tff(c_830, plain, (![A_149]: (k6_partfun1(A_149)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_149), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_149 | ~v1_funct_1(k6_partfun1(A_149)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_807])).
% 13.39/6.02  tff(c_834, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_767, c_830])).
% 13.39/6.02  tff(c_835, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_834])).
% 13.39/6.02  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.39/6.02  tff(c_80, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 13.39/6.02  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_901, plain, (![A_156, C_157, B_158]: (k6_partfun1(A_156)=k5_relat_1(C_157, k2_funct_1(C_157)) | k1_xboole_0=B_158 | ~v2_funct_1(C_157) | k2_relset_1(A_156, B_158, C_157)!=B_158 | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_158))) | ~v1_funct_2(C_157, A_156, B_158) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.39/6.02  tff(c_905, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_901])).
% 13.39/6.02  tff(c_913, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_905])).
% 13.39/6.02  tff(c_914, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_913])).
% 13.39/6.02  tff(c_16, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.39/6.02  tff(c_75, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_partfun1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 13.39/6.02  tff(c_924, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_914, c_75])).
% 13.39/6.02  tff(c_933, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_924])).
% 13.39/6.02  tff(c_980, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_933, c_80])).
% 13.39/6.02  tff(c_1006, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_980])).
% 13.39/6.02  tff(c_1008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_835, c_1006])).
% 13.39/6.02  tff(c_1010, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_834])).
% 13.39/6.02  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_123, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_114])).
% 13.39/6.02  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 13.39/6.02  tff(c_810, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_804])).
% 13.39/6.02  tff(c_821, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_810])).
% 13.39/6.02  tff(c_822, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_821])).
% 13.39/6.02  tff(c_827, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_822])).
% 13.39/6.02  tff(c_1013, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_827])).
% 13.39/6.02  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_157, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.39/6.02  tff(c_164, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_73, c_157])).
% 13.39/6.02  tff(c_181, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_167])).
% 13.39/6.02  tff(c_1589, plain, (![A_189, B_190, C_191, D_192]: (k2_relset_1(A_189, B_190, C_191)=B_190 | ~r2_relset_1(B_190, B_190, k1_partfun1(B_190, A_189, A_189, B_190, D_192, C_191), k6_partfun1(B_190)) | ~m1_subset_1(D_192, k1_zfmisc_1(k2_zfmisc_1(B_190, A_189))) | ~v1_funct_2(D_192, B_190, A_189) | ~v1_funct_1(D_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_2(C_191, A_189, B_190) | ~v1_funct_1(C_191))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.39/6.02  tff(c_1595, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_684, c_1589])).
% 13.39/6.02  tff(c_1599, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_164, c_181, c_1595])).
% 13.39/6.02  tff(c_1601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1013, c_1599])).
% 13.39/6.02  tff(c_1602, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_822])).
% 13.39/6.02  tff(c_789, plain, (![D_141, A_143, E_145, B_142, F_144, C_146]: (k1_partfun1(A_143, B_142, C_146, D_141, E_145, F_144)=k5_relat_1(E_145, F_144) | ~m1_subset_1(F_144, k1_zfmisc_1(k2_zfmisc_1(C_146, D_141))) | ~v1_funct_1(F_144) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.39/6.02  tff(c_795, plain, (![A_143, B_142, E_145]: (k1_partfun1(A_143, B_142, '#skF_2', '#skF_1', E_145, '#skF_4')=k5_relat_1(E_145, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))) | ~v1_funct_1(E_145))), inference(resolution, [status(thm)], [c_62, c_789])).
% 13.39/6.02  tff(c_1617, plain, (![A_193, B_194, E_195]: (k1_partfun1(A_193, B_194, '#skF_2', '#skF_1', E_195, '#skF_4')=k5_relat_1(E_195, '#skF_4') | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_funct_1(E_195))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_795])).
% 13.39/6.02  tff(c_1623, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1617])).
% 13.39/6.02  tff(c_1630, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_684, c_1623])).
% 13.39/6.02  tff(c_1644, plain, (![A_196, C_197, B_198]: (k6_partfun1(A_196)=k5_relat_1(C_197, k2_funct_1(C_197)) | k1_xboole_0=B_198 | ~v2_funct_1(C_197) | k2_relset_1(A_196, B_198, C_197)!=B_198 | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_198))) | ~v1_funct_2(C_197, A_196, B_198) | ~v1_funct_1(C_197))), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.39/6.02  tff(c_1648, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1644])).
% 13.39/6.02  tff(c_1656, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_1648])).
% 13.39/6.02  tff(c_1657, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_1656])).
% 13.39/6.02  tff(c_1667, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1657, c_75])).
% 13.39/6.02  tff(c_1676, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_1667])).
% 13.39/6.02  tff(c_1720, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1676, c_80])).
% 13.39/6.02  tff(c_1743, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1720])).
% 13.39/6.02  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.39/6.02  tff(c_1603, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_822])).
% 13.39/6.02  tff(c_1604, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1603, c_181])).
% 13.39/6.02  tff(c_1778, plain, (![B_199, C_200, A_201]: (k6_partfun1(B_199)=k5_relat_1(k2_funct_1(C_200), C_200) | k1_xboole_0=B_199 | ~v2_funct_1(C_200) | k2_relset_1(A_201, B_199, C_200)!=B_199 | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_199))) | ~v1_funct_2(C_200, A_201, B_199) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.39/6.02  tff(c_1784, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1778])).
% 13.39/6.02  tff(c_1794, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1604, c_1784])).
% 13.39/6.02  tff(c_1795, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_1794])).
% 13.39/6.02  tff(c_1907, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1743, c_1795])).
% 13.39/6.02  tff(c_1908, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1907])).
% 13.39/6.02  tff(c_10, plain, (![A_7]: (k5_relat_1(k6_relat_1(k1_relat_1(A_7)), A_7)=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.39/6.02  tff(c_134, plain, (![A_60]: (k5_relat_1(k6_partfun1(k1_relat_1(A_60)), A_60)=A_60 | ~v1_relat_1(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 13.39/6.02  tff(c_143, plain, (![A_6]: (k5_relat_1(k6_partfun1(A_6), k6_partfun1(A_6))=k6_partfun1(A_6) | ~v1_relat_1(k6_partfun1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_134])).
% 13.39/6.02  tff(c_147, plain, (![A_6]: (k5_relat_1(k6_partfun1(A_6), k6_partfun1(A_6))=k6_partfun1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_143])).
% 13.39/6.02  tff(c_12, plain, (![A_8, B_10]: (v2_funct_1(A_8) | k6_relat_1(k1_relat_1(A_8))!=k5_relat_1(A_8, B_10) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.39/6.02  tff(c_218, plain, (![A_72, B_73]: (v2_funct_1(A_72) | k6_partfun1(k1_relat_1(A_72))!=k5_relat_1(A_72, B_73) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 13.39/6.02  tff(c_224, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)) | k6_partfun1(k1_relat_1(k6_partfun1(A_6)))!=k6_partfun1(A_6) | ~v1_funct_1(k6_partfun1(A_6)) | ~v1_relat_1(k6_partfun1(A_6)) | ~v1_funct_1(k6_partfun1(A_6)) | ~v1_relat_1(k6_partfun1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_147, c_218])).
% 13.39/6.02  tff(c_231, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)) | ~v1_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_126, c_80, c_224])).
% 13.39/6.02  tff(c_1692, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1(k6_partfun1(k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1676, c_231])).
% 13.39/6.02  tff(c_1733, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_767, c_1676, c_1692])).
% 13.39/6.02  tff(c_2045, plain, (![E_216, A_217, B_220, D_219, C_218]: (k1_xboole_0=C_218 | v2_funct_1(E_216) | k2_relset_1(A_217, B_220, D_219)!=B_220 | ~v2_funct_1(k1_partfun1(A_217, B_220, B_220, C_218, D_219, E_216)) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(B_220, C_218))) | ~v1_funct_2(E_216, B_220, C_218) | ~v1_funct_1(E_216) | ~m1_subset_1(D_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_220))) | ~v1_funct_2(D_219, A_217, B_220) | ~v1_funct_1(D_219))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.39/6.02  tff(c_2047, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_684, c_2045])).
% 13.39/6.02  tff(c_2049, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_1733, c_60, c_2047])).
% 13.39/6.02  tff(c_2051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1908, c_54, c_2049])).
% 13.39/6.02  tff(c_2053, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1907])).
% 13.39/6.02  tff(c_1650, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1644])).
% 13.39/6.02  tff(c_1660, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1604, c_1650])).
% 13.39/6.02  tff(c_1661, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_1660])).
% 13.39/6.02  tff(c_1746, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1661])).
% 13.39/6.02  tff(c_1775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1743, c_1746])).
% 13.39/6.02  tff(c_1776, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1661])).
% 13.39/6.02  tff(c_2128, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_1776])).
% 13.39/6.02  tff(c_2134, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2128, c_75])).
% 13.39/6.02  tff(c_2143, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_66, c_2053, c_2134])).
% 13.39/6.02  tff(c_2187, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2143, c_80])).
% 13.39/6.02  tff(c_2206, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2187])).
% 13.39/6.02  tff(c_1799, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1743, c_1603])).
% 13.39/6.02  tff(c_74, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_partfun1(k2_relat_1(A_12))!=k5_relat_1(B_14, A_12) | k2_relat_1(B_14)!=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 13.39/6.02  tff(c_1836, plain, (![B_14]: (k2_funct_1('#skF_4')=B_14 | k5_relat_1(B_14, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_14)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1799, c_74])).
% 13.39/6.02  tff(c_1840, plain, (![B_14]: (k2_funct_1('#skF_4')=B_14 | k5_relat_1(B_14, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_14)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_66, c_1836])).
% 13.39/6.02  tff(c_13100, plain, (![B_540]: (k2_funct_1('#skF_4')=B_540 | k5_relat_1(B_540, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_540)!='#skF_2' | ~v1_funct_1(B_540) | ~v1_relat_1(B_540))), inference(demodulation, [status(thm), theory('equality')], [c_2053, c_2206, c_1840])).
% 13.39/6.02  tff(c_13427, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_13100])).
% 13.39/6.02  tff(c_13646, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_180, c_1630, c_13427])).
% 13.39/6.02  tff(c_13649, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13646, c_2128])).
% 13.39/6.02  tff(c_13652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1602, c_13649])).
% 13.39/6.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.39/6.02  
% 13.39/6.02  Inference rules
% 13.39/6.02  ----------------------
% 13.39/6.02  #Ref     : 0
% 13.39/6.02  #Sup     : 2804
% 13.39/6.02  #Fact    : 0
% 13.39/6.02  #Define  : 0
% 13.39/6.02  #Split   : 43
% 13.39/6.02  #Chain   : 0
% 13.39/6.02  #Close   : 0
% 13.39/6.02  
% 13.39/6.02  Ordering : KBO
% 13.39/6.02  
% 13.39/6.02  Simplification rules
% 13.39/6.02  ----------------------
% 13.39/6.02  #Subsume      : 243
% 13.39/6.02  #Demod        : 7900
% 13.39/6.02  #Tautology    : 546
% 13.39/6.02  #SimpNegUnit  : 404
% 13.39/6.02  #BackRed      : 56
% 13.39/6.02  
% 13.39/6.02  #Partial instantiations: 0
% 13.39/6.02  #Strategies tried      : 1
% 13.39/6.02  
% 13.39/6.02  Timing (in seconds)
% 13.39/6.02  ----------------------
% 13.39/6.02  Preprocessing        : 0.40
% 13.39/6.02  Parsing              : 0.22
% 13.39/6.02  CNF conversion       : 0.03
% 13.39/6.02  Main loop            : 4.76
% 13.39/6.02  Inferencing          : 0.99
% 13.39/6.02  Reduction            : 2.56
% 13.39/6.02  Demodulation         : 2.19
% 13.39/6.02  BG Simplification    : 0.09
% 13.39/6.02  Subsumption          : 0.91
% 13.39/6.02  Abstraction          : 0.16
% 13.39/6.02  MUC search           : 0.00
% 13.39/6.02  Cooper               : 0.00
% 13.39/6.02  Total                : 5.23
% 13.39/6.02  Index Insertion      : 0.00
% 13.39/6.03  Index Deletion       : 0.00
% 13.39/6.03  Index Matching       : 0.00
% 13.39/6.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
