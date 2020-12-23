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
% DateTime   : Thu Dec  3 10:13:25 EST 2020

% Result     : Theorem 9.90s
% Output     : CNFRefutation 9.90s
% Verified   : 
% Statistics : Number of formulae       :  192 (1907 expanded)
%              Number of leaves         :   41 ( 682 expanded)
%              Depth                    :   25
%              Number of atoms          :  475 (7984 expanded)
%              Number of equality atoms :  185 (2826 expanded)
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

tff(f_192,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
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

tff(f_156,axiom,(
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

tff(f_166,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_114,axiom,(
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

tff(f_40,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_140,axiom,(
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

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_402,plain,(
    ! [D_91,A_92,B_95,E_96,F_94,C_93] :
      ( k1_partfun1(A_92,B_95,C_93,D_91,E_96,F_94) = k5_relat_1(E_96,F_94)
      | ~ m1_subset_1(F_94,k1_zfmisc_1(k2_zfmisc_1(C_93,D_91)))
      | ~ v1_funct_1(F_94)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_92,B_95)))
      | ~ v1_funct_1(E_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_412,plain,(
    ! [A_92,B_95,E_96] :
      ( k1_partfun1(A_92,B_95,'#skF_2','#skF_1',E_96,'#skF_4') = k5_relat_1(E_96,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_92,B_95)))
      | ~ v1_funct_1(E_96) ) ),
    inference(resolution,[status(thm)],[c_64,c_402])).

tff(c_663,plain,(
    ! [A_109,B_110,E_111] :
      ( k1_partfun1(A_109,B_110,'#skF_2','#skF_1',E_111,'#skF_4') = k5_relat_1(E_111,'#skF_4')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_412])).

tff(c_672,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_663])).

tff(c_680,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_672])).

tff(c_26,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_241,plain,(
    ! [D_70,C_71,A_72,B_73] :
      ( D_70 = C_71
      | ~ r2_relset_1(A_72,B_73,C_71,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_251,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_241])).

tff(c_270,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_251])).

tff(c_315,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_685,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_315])).

tff(c_701,plain,(
    ! [A_112,D_116,F_115,E_114,C_113,B_117] :
      ( m1_subset_1(k1_partfun1(A_112,B_117,C_113,D_116,E_114,F_115),k1_zfmisc_1(k2_zfmisc_1(A_112,D_116)))
      | ~ m1_subset_1(F_115,k1_zfmisc_1(k2_zfmisc_1(C_113,D_116)))
      | ~ v1_funct_1(F_115)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_117)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_735,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_701])).

tff(c_758,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_735])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_758])).

tff(c_761,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_806,plain,(
    ! [A_122,D_126,E_124,C_123,B_127,F_125] :
      ( v1_funct_1(k1_partfun1(A_122,B_127,C_123,D_126,E_124,F_125))
      | ~ m1_subset_1(F_125,k1_zfmisc_1(k2_zfmisc_1(C_123,D_126)))
      | ~ v1_funct_1(F_125)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_127)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_816,plain,(
    ! [A_122,B_127,E_124] :
      ( v1_funct_1(k1_partfun1(A_122,B_127,'#skF_2','#skF_1',E_124,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_127)))
      | ~ v1_funct_1(E_124) ) ),
    inference(resolution,[status(thm)],[c_64,c_806])).

tff(c_855,plain,(
    ! [A_131,B_132,E_133] :
      ( v1_funct_1(k1_partfun1(A_131,B_132,'#skF_2','#skF_1',E_133,'#skF_4'))
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(E_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_816])).

tff(c_867,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_855])).

tff(c_878,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_761,c_867])).

tff(c_30,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_114,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [A_24] :
      ( v1_relat_1(k6_partfun1(A_24))
      | ~ v1_relat_1(k2_zfmisc_1(A_24,A_24)) ) ),
    inference(resolution,[status(thm)],[c_26,c_114])).

tff(c_126,plain,(
    ! [A_24] : v1_relat_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_117])).

tff(c_120,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_114])).

tff(c_129,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_120])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_157,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_163,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_157])).

tff(c_170,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_163])).

tff(c_12,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_770,plain,(
    ! [A_118,B_119] :
      ( k2_funct_1(A_118) = B_119
      | k6_partfun1(k2_relat_1(A_118)) != k5_relat_1(B_119,A_118)
      | k2_relat_1(B_119) != k1_relat_1(A_118)
      | ~ v2_funct_1(A_118)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_772,plain,(
    ! [B_119] :
      ( k2_funct_1('#skF_3') = B_119
      | k5_relat_1(B_119,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_119) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_770])).

tff(c_779,plain,(
    ! [B_120] :
      ( k2_funct_1('#skF_3') = B_120
      | k5_relat_1(B_120,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_120) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_74,c_58,c_772])).

tff(c_782,plain,(
    ! [A_24] :
      ( k6_partfun1(A_24) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_24),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_24)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_126,c_779])).

tff(c_793,plain,(
    ! [A_24] :
      ( k6_partfun1(A_24) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_24),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_24
      | ~ v1_funct_1(k6_partfun1(A_24)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_782])).

tff(c_885,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_878,c_793])).

tff(c_910,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_885])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1037,plain,(
    ! [A_151,C_152,B_153] :
      ( k6_partfun1(A_151) = k5_relat_1(C_152,k2_funct_1(C_152))
      | k1_xboole_0 = B_153
      | ~ v2_funct_1(C_152)
      | k2_relset_1(A_151,B_153,C_152) != B_153
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_153)))
      | ~ v1_funct_2(C_152,A_151,B_153)
      | ~ v1_funct_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1045,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1037])).

tff(c_1058,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_1045])).

tff(c_1059,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1058])).

tff(c_48,plain,(
    ! [A_46] :
      ( v1_funct_2(A_46,k1_relat_1(A_46),k2_relat_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_175,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_48])).

tff(c_179,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_74,c_175])).

tff(c_194,plain,(
    ! [A_69] :
      ( m1_subset_1(A_69,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_69),k2_relat_1(A_69))))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_205,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_194])).

tff(c_218,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_74,c_205])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_225,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_218,c_14])).

tff(c_232,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_225])).

tff(c_1039,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_218,c_1037])).

tff(c_1050,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_179,c_232,c_58,c_1039])).

tff(c_1051,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1050])).

tff(c_1068,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_1051])).

tff(c_1100,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_77])).

tff(c_1125,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1100])).

tff(c_1127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_910,c_1125])).

tff(c_1129,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_885])).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_123,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_114])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_785,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_779])).

tff(c_796,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_785])).

tff(c_797,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_796])).

tff(c_802,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_1134,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_802])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_146,plain,(
    ! [A_61,B_62,D_63] :
      ( r2_relset_1(A_61,B_62,D_63,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_153,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_171,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_157])).

tff(c_1807,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k2_relset_1(A_185,B_186,C_187) = B_186
      | ~ r2_relset_1(B_186,B_186,k1_partfun1(B_186,A_185,A_185,B_186,D_188,C_187),k6_partfun1(B_186))
      | ~ m1_subset_1(D_188,k1_zfmisc_1(k2_zfmisc_1(B_186,A_185)))
      | ~ v1_funct_2(D_188,B_186,A_185)
      | ~ v1_funct_1(D_188)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_2(C_187,A_185,B_186)
      | ~ v1_funct_1(C_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1813,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_1807])).

tff(c_1817,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_153,c_171,c_1813])).

tff(c_1819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1134,c_1817])).

tff(c_1820,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_1995,plain,(
    ! [F_206,D_203,C_205,A_204,E_208,B_207] :
      ( k1_partfun1(A_204,B_207,C_205,D_203,E_208,F_206) = k5_relat_1(E_208,F_206)
      | ~ m1_subset_1(F_206,k1_zfmisc_1(k2_zfmisc_1(C_205,D_203)))
      | ~ v1_funct_1(F_206)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_204,B_207)))
      | ~ v1_funct_1(E_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2007,plain,(
    ! [A_204,B_207,E_208] :
      ( k1_partfun1(A_204,B_207,'#skF_2','#skF_1',E_208,'#skF_4') = k5_relat_1(E_208,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_204,B_207)))
      | ~ v1_funct_1(E_208) ) ),
    inference(resolution,[status(thm)],[c_64,c_1995])).

tff(c_2834,plain,(
    ! [A_248,B_249,E_250] :
      ( k1_partfun1(A_248,B_249,'#skF_2','#skF_1',E_250,'#skF_4') = k5_relat_1(E_250,'#skF_4')
      | ~ m1_subset_1(E_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ v1_funct_1(E_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2007])).

tff(c_2843,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2834])).

tff(c_2851,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_761,c_2843])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1821,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_1822,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1821,c_171])).

tff(c_2065,plain,(
    ! [B_212,C_213,A_214] :
      ( k6_partfun1(B_212) = k5_relat_1(k2_funct_1(C_213),C_213)
      | k1_xboole_0 = B_212
      | ~ v2_funct_1(C_213)
      | k2_relset_1(A_214,B_212,C_213) != B_212
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_214,B_212)))
      | ~ v1_funct_2(C_213,A_214,B_212)
      | ~ v1_funct_1(C_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2077,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2065])).

tff(c_2095,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1822,c_2077])).

tff(c_2096,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2095])).

tff(c_2107,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2096])).

tff(c_2122,plain,(
    ! [A_216,C_217,B_218] :
      ( k6_partfun1(A_216) = k5_relat_1(C_217,k2_funct_1(C_217))
      | k1_xboole_0 = B_218
      | ~ v2_funct_1(C_217)
      | k2_relset_1(A_216,B_218,C_217) != B_218
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_216,B_218)))
      | ~ v1_funct_2(C_217,A_216,B_218)
      | ~ v1_funct_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2132,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2122])).

tff(c_2148,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_2132])).

tff(c_2149,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2148])).

tff(c_2126,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_218,c_2122])).

tff(c_2140,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_179,c_232,c_58,c_2126])).

tff(c_2141,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2140])).

tff(c_2158,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2149,c_2141])).

tff(c_2185,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2158,c_77])).

tff(c_2205,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2185])).

tff(c_2207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2107,c_2205])).

tff(c_2209,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2096])).

tff(c_2220,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_1821])).

tff(c_2818,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2220,c_48])).

tff(c_2832,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_68,c_2818])).

tff(c_212,plain,(
    ! [A_69] :
      ( k2_relset_1(k1_relat_1(A_69),k2_relat_1(A_69),A_69) = k2_relat_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_194,c_14])).

tff(c_2809,plain,
    ( k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') = k2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2220,c_212])).

tff(c_2826,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_68,c_2220,c_2809])).

tff(c_2208,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2096])).

tff(c_2261,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2208])).

tff(c_10,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10])).

tff(c_2787,plain,(
    ! [D_245,B_244,A_243,C_247,E_246] :
      ( k1_xboole_0 = C_247
      | v2_funct_1(E_246)
      | k2_relset_1(A_243,B_244,D_245) != B_244
      | ~ v2_funct_1(k1_partfun1(A_243,B_244,B_244,C_247,D_245,E_246))
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(B_244,C_247)))
      | ~ v1_funct_2(E_246,B_244,C_247)
      | ~ v1_funct_1(E_246)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_2(D_245,A_243,B_244)
      | ~ v1_funct_1(D_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2791,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_761,c_2787])).

tff(c_2796,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_76,c_62,c_2791])).

tff(c_2798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2261,c_56,c_2796])).

tff(c_2800,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2208])).

tff(c_2219,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_1822])).

tff(c_2873,plain,(
    ! [A_251,C_252,B_253] :
      ( k6_partfun1(A_251) = k5_relat_1(C_252,k2_funct_1(C_252))
      | k1_xboole_0 = B_253
      | ~ v2_funct_1(C_252)
      | k2_relset_1(A_251,B_253,C_252) != B_253
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_251,B_253)))
      | ~ v1_funct_2(C_252,A_251,B_253)
      | ~ v1_funct_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2881,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2873])).

tff(c_2892,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2219,c_2800,c_2881])).

tff(c_2893,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2892])).

tff(c_46,plain,(
    ! [A_46] :
      ( m1_subset_1(A_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_46),k2_relat_1(A_46))))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1834,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1821,c_46])).

tff(c_1847,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_68,c_1834])).

tff(c_2216,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_1847])).

tff(c_44,plain,(
    ! [A_43,C_45,B_44] :
      ( k6_partfun1(A_43) = k5_relat_1(C_45,k2_funct_1(C_45))
      | k1_xboole_0 = B_44
      | ~ v2_funct_1(C_45)
      | k2_relset_1(A_43,B_44,C_45) != B_44
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(C_45,A_43,B_44)
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2918,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),'#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2216,c_44])).

tff(c_2947,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2832,c_2826,c_2800,c_2893,c_2918])).

tff(c_2948,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2947])).

tff(c_3063,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2948,c_77])).

tff(c_3079,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3063])).

tff(c_75,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_partfun1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_2806,plain,(
    ! [B_10] :
      ( k2_funct_1('#skF_4') = B_10
      | k5_relat_1(B_10,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_10) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2220,c_75])).

tff(c_2824,plain,(
    ! [B_10] :
      ( k2_funct_1('#skF_4') = B_10
      | k5_relat_1(B_10,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_10) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_68,c_2800,c_2806])).

tff(c_10230,plain,(
    ! [B_475] :
      ( k2_funct_1('#skF_4') = B_475
      | k5_relat_1(B_475,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_475) != '#skF_2'
      | ~ v1_funct_1(B_475)
      | ~ v1_relat_1(B_475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3079,c_2824])).

tff(c_10458,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_10230])).

tff(c_10641,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_170,c_2851,c_10458])).

tff(c_10646,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10641,c_2893])).

tff(c_10651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1820,c_10646])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.90/3.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.90/3.87  
% 9.90/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.90/3.87  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.90/3.87  
% 9.90/3.87  %Foreground sorts:
% 9.90/3.87  
% 9.90/3.87  
% 9.90/3.87  %Background operators:
% 9.90/3.87  
% 9.90/3.87  
% 9.90/3.87  %Foreground operators:
% 9.90/3.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.90/3.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.90/3.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.90/3.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.90/3.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.90/3.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.90/3.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.90/3.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.90/3.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.90/3.87  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.90/3.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.90/3.87  tff('#skF_2', type, '#skF_2': $i).
% 9.90/3.87  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.90/3.87  tff('#skF_3', type, '#skF_3': $i).
% 9.90/3.87  tff('#skF_1', type, '#skF_1': $i).
% 9.90/3.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.90/3.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.90/3.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.90/3.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.90/3.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.90/3.87  tff('#skF_4', type, '#skF_4': $i).
% 9.90/3.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.90/3.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.90/3.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.90/3.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.90/3.87  
% 9.90/3.90  tff(f_192, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.90/3.90  tff(f_95, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.90/3.90  tff(f_85, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.90/3.90  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.90/3.90  tff(f_81, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.90/3.90  tff(f_97, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.90/3.90  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.90/3.90  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.90/3.90  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.90/3.90  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.90/3.90  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 9.90/3.90  tff(f_156, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 9.90/3.90  tff(f_166, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 9.90/3.90  tff(f_114, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.90/3.90  tff(f_40, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 9.90/3.90  tff(f_140, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 9.90/3.90  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_402, plain, (![D_91, A_92, B_95, E_96, F_94, C_93]: (k1_partfun1(A_92, B_95, C_93, D_91, E_96, F_94)=k5_relat_1(E_96, F_94) | ~m1_subset_1(F_94, k1_zfmisc_1(k2_zfmisc_1(C_93, D_91))) | ~v1_funct_1(F_94) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_92, B_95))) | ~v1_funct_1(E_96))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.90/3.90  tff(c_412, plain, (![A_92, B_95, E_96]: (k1_partfun1(A_92, B_95, '#skF_2', '#skF_1', E_96, '#skF_4')=k5_relat_1(E_96, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_92, B_95))) | ~v1_funct_1(E_96))), inference(resolution, [status(thm)], [c_64, c_402])).
% 9.90/3.90  tff(c_663, plain, (![A_109, B_110, E_111]: (k1_partfun1(A_109, B_110, '#skF_2', '#skF_1', E_111, '#skF_4')=k5_relat_1(E_111, '#skF_4') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_1(E_111))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_412])).
% 9.90/3.90  tff(c_672, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_663])).
% 9.90/3.90  tff(c_680, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_672])).
% 9.90/3.90  tff(c_26, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.90/3.90  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_241, plain, (![D_70, C_71, A_72, B_73]: (D_70=C_71 | ~r2_relset_1(A_72, B_73, C_71, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.90/3.90  tff(c_251, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_241])).
% 9.90/3.90  tff(c_270, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_251])).
% 9.90/3.90  tff(c_315, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_270])).
% 9.90/3.90  tff(c_685, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_315])).
% 9.90/3.90  tff(c_701, plain, (![A_112, D_116, F_115, E_114, C_113, B_117]: (m1_subset_1(k1_partfun1(A_112, B_117, C_113, D_116, E_114, F_115), k1_zfmisc_1(k2_zfmisc_1(A_112, D_116))) | ~m1_subset_1(F_115, k1_zfmisc_1(k2_zfmisc_1(C_113, D_116))) | ~v1_funct_1(F_115) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_117))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.90/3.90  tff(c_735, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_680, c_701])).
% 9.90/3.90  tff(c_758, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_735])).
% 9.90/3.90  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_758])).
% 9.90/3.90  tff(c_761, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_270])).
% 9.90/3.90  tff(c_806, plain, (![A_122, D_126, E_124, C_123, B_127, F_125]: (v1_funct_1(k1_partfun1(A_122, B_127, C_123, D_126, E_124, F_125)) | ~m1_subset_1(F_125, k1_zfmisc_1(k2_zfmisc_1(C_123, D_126))) | ~v1_funct_1(F_125) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_127))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.90/3.90  tff(c_816, plain, (![A_122, B_127, E_124]: (v1_funct_1(k1_partfun1(A_122, B_127, '#skF_2', '#skF_1', E_124, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_127))) | ~v1_funct_1(E_124))), inference(resolution, [status(thm)], [c_64, c_806])).
% 9.90/3.90  tff(c_855, plain, (![A_131, B_132, E_133]: (v1_funct_1(k1_partfun1(A_131, B_132, '#skF_2', '#skF_1', E_133, '#skF_4')) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(E_133))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_816])).
% 9.90/3.90  tff(c_867, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_855])).
% 9.90/3.90  tff(c_878, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_761, c_867])).
% 9.90/3.90  tff(c_30, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.90/3.90  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.90/3.90  tff(c_77, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8])).
% 9.90/3.90  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.90/3.90  tff(c_114, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.90/3.90  tff(c_117, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)) | ~v1_relat_1(k2_zfmisc_1(A_24, A_24)))), inference(resolution, [status(thm)], [c_26, c_114])).
% 9.90/3.90  tff(c_126, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_117])).
% 9.90/3.90  tff(c_120, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_114])).
% 9.90/3.90  tff(c_129, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_120])).
% 9.90/3.90  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_157, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.90/3.90  tff(c_163, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_157])).
% 9.90/3.90  tff(c_170, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_163])).
% 9.90/3.90  tff(c_12, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.90/3.90  tff(c_770, plain, (![A_118, B_119]: (k2_funct_1(A_118)=B_119 | k6_partfun1(k2_relat_1(A_118))!=k5_relat_1(B_119, A_118) | k2_relat_1(B_119)!=k1_relat_1(A_118) | ~v2_funct_1(A_118) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 9.90/3.90  tff(c_772, plain, (![B_119]: (k2_funct_1('#skF_3')=B_119 | k5_relat_1(B_119, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_119)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_770])).
% 9.90/3.90  tff(c_779, plain, (![B_120]: (k2_funct_1('#skF_3')=B_120 | k5_relat_1(B_120, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_120)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_74, c_58, c_772])).
% 9.90/3.90  tff(c_782, plain, (![A_24]: (k6_partfun1(A_24)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_24), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_24))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_126, c_779])).
% 9.90/3.90  tff(c_793, plain, (![A_24]: (k6_partfun1(A_24)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_24), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_24 | ~v1_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_782])).
% 9.90/3.90  tff(c_885, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_878, c_793])).
% 9.90/3.90  tff(c_910, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_885])).
% 9.90/3.90  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_1037, plain, (![A_151, C_152, B_153]: (k6_partfun1(A_151)=k5_relat_1(C_152, k2_funct_1(C_152)) | k1_xboole_0=B_153 | ~v2_funct_1(C_152) | k2_relset_1(A_151, B_153, C_152)!=B_153 | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_153))) | ~v1_funct_2(C_152, A_151, B_153) | ~v1_funct_1(C_152))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.90/3.90  tff(c_1045, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1037])).
% 9.90/3.90  tff(c_1058, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_1045])).
% 9.90/3.90  tff(c_1059, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_1058])).
% 9.90/3.90  tff(c_48, plain, (![A_46]: (v1_funct_2(A_46, k1_relat_1(A_46), k2_relat_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.90/3.90  tff(c_175, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_170, c_48])).
% 9.90/3.90  tff(c_179, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_74, c_175])).
% 9.90/3.90  tff(c_194, plain, (![A_69]: (m1_subset_1(A_69, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_69), k2_relat_1(A_69)))) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.90/3.90  tff(c_205, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_170, c_194])).
% 9.90/3.90  tff(c_218, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_74, c_205])).
% 9.90/3.90  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.90/3.90  tff(c_225, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_218, c_14])).
% 9.90/3.90  tff(c_232, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_225])).
% 9.90/3.90  tff(c_1039, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_218, c_1037])).
% 9.90/3.90  tff(c_1050, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_179, c_232, c_58, c_1039])).
% 9.90/3.90  tff(c_1051, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1050])).
% 9.90/3.90  tff(c_1068, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1059, c_1051])).
% 9.90/3.90  tff(c_1100, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1068, c_77])).
% 9.90/3.90  tff(c_1125, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1100])).
% 9.90/3.90  tff(c_1127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_910, c_1125])).
% 9.90/3.90  tff(c_1129, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_885])).
% 9.90/3.90  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_123, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_114])).
% 9.90/3.90  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 9.90/3.90  tff(c_785, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_779])).
% 9.90/3.90  tff(c_796, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_785])).
% 9.90/3.90  tff(c_797, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_796])).
% 9.90/3.90  tff(c_802, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_797])).
% 9.90/3.90  tff(c_1134, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_802])).
% 9.90/3.90  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_146, plain, (![A_61, B_62, D_63]: (r2_relset_1(A_61, B_62, D_63, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.90/3.90  tff(c_153, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_26, c_146])).
% 9.90/3.90  tff(c_171, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_157])).
% 9.90/3.90  tff(c_1807, plain, (![A_185, B_186, C_187, D_188]: (k2_relset_1(A_185, B_186, C_187)=B_186 | ~r2_relset_1(B_186, B_186, k1_partfun1(B_186, A_185, A_185, B_186, D_188, C_187), k6_partfun1(B_186)) | ~m1_subset_1(D_188, k1_zfmisc_1(k2_zfmisc_1(B_186, A_185))) | ~v1_funct_2(D_188, B_186, A_185) | ~v1_funct_1(D_188) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_2(C_187, A_185, B_186) | ~v1_funct_1(C_187))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.90/3.90  tff(c_1813, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_761, c_1807])).
% 9.90/3.90  tff(c_1817, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_153, c_171, c_1813])).
% 9.90/3.90  tff(c_1819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1134, c_1817])).
% 9.90/3.90  tff(c_1820, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_797])).
% 9.90/3.90  tff(c_1995, plain, (![F_206, D_203, C_205, A_204, E_208, B_207]: (k1_partfun1(A_204, B_207, C_205, D_203, E_208, F_206)=k5_relat_1(E_208, F_206) | ~m1_subset_1(F_206, k1_zfmisc_1(k2_zfmisc_1(C_205, D_203))) | ~v1_funct_1(F_206) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_204, B_207))) | ~v1_funct_1(E_208))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.90/3.90  tff(c_2007, plain, (![A_204, B_207, E_208]: (k1_partfun1(A_204, B_207, '#skF_2', '#skF_1', E_208, '#skF_4')=k5_relat_1(E_208, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_204, B_207))) | ~v1_funct_1(E_208))), inference(resolution, [status(thm)], [c_64, c_1995])).
% 9.90/3.90  tff(c_2834, plain, (![A_248, B_249, E_250]: (k1_partfun1(A_248, B_249, '#skF_2', '#skF_1', E_250, '#skF_4')=k5_relat_1(E_250, '#skF_4') | ~m1_subset_1(E_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~v1_funct_1(E_250))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2007])).
% 9.90/3.90  tff(c_2843, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2834])).
% 9.90/3.90  tff(c_2851, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_761, c_2843])).
% 9.90/3.90  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.90/3.90  tff(c_1821, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_797])).
% 9.90/3.90  tff(c_1822, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1821, c_171])).
% 9.90/3.90  tff(c_2065, plain, (![B_212, C_213, A_214]: (k6_partfun1(B_212)=k5_relat_1(k2_funct_1(C_213), C_213) | k1_xboole_0=B_212 | ~v2_funct_1(C_213) | k2_relset_1(A_214, B_212, C_213)!=B_212 | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_214, B_212))) | ~v1_funct_2(C_213, A_214, B_212) | ~v1_funct_1(C_213))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.90/3.90  tff(c_2077, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2065])).
% 9.90/3.90  tff(c_2095, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1822, c_2077])).
% 9.90/3.90  tff(c_2096, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_2095])).
% 9.90/3.90  tff(c_2107, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2096])).
% 9.90/3.90  tff(c_2122, plain, (![A_216, C_217, B_218]: (k6_partfun1(A_216)=k5_relat_1(C_217, k2_funct_1(C_217)) | k1_xboole_0=B_218 | ~v2_funct_1(C_217) | k2_relset_1(A_216, B_218, C_217)!=B_218 | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_216, B_218))) | ~v1_funct_2(C_217, A_216, B_218) | ~v1_funct_1(C_217))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.90/3.90  tff(c_2132, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2122])).
% 9.90/3.90  tff(c_2148, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_2132])).
% 9.90/3.90  tff(c_2149, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_2148])).
% 9.90/3.90  tff(c_2126, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_218, c_2122])).
% 9.90/3.90  tff(c_2140, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_179, c_232, c_58, c_2126])).
% 9.90/3.90  tff(c_2141, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_2140])).
% 9.90/3.90  tff(c_2158, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2149, c_2141])).
% 9.90/3.90  tff(c_2185, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2158, c_77])).
% 9.90/3.90  tff(c_2205, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2185])).
% 9.90/3.90  tff(c_2207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2107, c_2205])).
% 9.90/3.90  tff(c_2209, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2096])).
% 9.90/3.90  tff(c_2220, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_1821])).
% 9.90/3.90  tff(c_2818, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2220, c_48])).
% 9.90/3.90  tff(c_2832, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_68, c_2818])).
% 9.90/3.90  tff(c_212, plain, (![A_69]: (k2_relset_1(k1_relat_1(A_69), k2_relat_1(A_69), A_69)=k2_relat_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_194, c_14])).
% 9.90/3.90  tff(c_2809, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')=k2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2220, c_212])).
% 9.90/3.90  tff(c_2826, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_68, c_2220, c_2809])).
% 9.90/3.90  tff(c_2208, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2096])).
% 9.90/3.90  tff(c_2261, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2208])).
% 9.90/3.90  tff(c_10, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.90/3.90  tff(c_76, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10])).
% 9.90/3.90  tff(c_2787, plain, (![D_245, B_244, A_243, C_247, E_246]: (k1_xboole_0=C_247 | v2_funct_1(E_246) | k2_relset_1(A_243, B_244, D_245)!=B_244 | ~v2_funct_1(k1_partfun1(A_243, B_244, B_244, C_247, D_245, E_246)) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(B_244, C_247))) | ~v1_funct_2(E_246, B_244, C_247) | ~v1_funct_1(E_246) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_2(D_245, A_243, B_244) | ~v1_funct_1(D_245))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.90/3.90  tff(c_2791, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_761, c_2787])).
% 9.90/3.90  tff(c_2796, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_76, c_62, c_2791])).
% 9.90/3.90  tff(c_2798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2261, c_56, c_2796])).
% 9.90/3.90  tff(c_2800, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2208])).
% 9.90/3.90  tff(c_2219, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_1822])).
% 9.90/3.90  tff(c_2873, plain, (![A_251, C_252, B_253]: (k6_partfun1(A_251)=k5_relat_1(C_252, k2_funct_1(C_252)) | k1_xboole_0=B_253 | ~v2_funct_1(C_252) | k2_relset_1(A_251, B_253, C_252)!=B_253 | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_251, B_253))) | ~v1_funct_2(C_252, A_251, B_253) | ~v1_funct_1(C_252))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.90/3.90  tff(c_2881, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2873])).
% 9.90/3.90  tff(c_2892, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_2219, c_2800, c_2881])).
% 9.90/3.90  tff(c_2893, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_2892])).
% 9.90/3.90  tff(c_46, plain, (![A_46]: (m1_subset_1(A_46, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_46), k2_relat_1(A_46)))) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.90/3.90  tff(c_1834, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_relat_1('#skF_3')))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1821, c_46])).
% 9.90/3.90  tff(c_1847, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_68, c_1834])).
% 9.90/3.90  tff(c_2216, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_1847])).
% 9.90/3.90  tff(c_44, plain, (![A_43, C_45, B_44]: (k6_partfun1(A_43)=k5_relat_1(C_45, k2_funct_1(C_45)) | k1_xboole_0=B_44 | ~v2_funct_1(C_45) | k2_relset_1(A_43, B_44, C_45)!=B_44 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(C_45, A_43, B_44) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.90/3.90  tff(c_2918, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2216, c_44])).
% 9.90/3.90  tff(c_2947, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2832, c_2826, c_2800, c_2893, c_2918])).
% 9.90/3.90  tff(c_2948, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_2947])).
% 9.90/3.90  tff(c_3063, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2948, c_77])).
% 9.90/3.90  tff(c_3079, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3063])).
% 9.90/3.90  tff(c_75, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_partfun1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 9.90/3.90  tff(c_2806, plain, (![B_10]: (k2_funct_1('#skF_4')=B_10 | k5_relat_1(B_10, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_10)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2220, c_75])).
% 9.90/3.90  tff(c_2824, plain, (![B_10]: (k2_funct_1('#skF_4')=B_10 | k5_relat_1(B_10, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_10)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_68, c_2800, c_2806])).
% 9.90/3.90  tff(c_10230, plain, (![B_475]: (k2_funct_1('#skF_4')=B_475 | k5_relat_1(B_475, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_475)!='#skF_2' | ~v1_funct_1(B_475) | ~v1_relat_1(B_475))), inference(demodulation, [status(thm), theory('equality')], [c_3079, c_2824])).
% 9.90/3.90  tff(c_10458, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_10230])).
% 9.90/3.90  tff(c_10641, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_170, c_2851, c_10458])).
% 9.90/3.90  tff(c_10646, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10641, c_2893])).
% 9.90/3.90  tff(c_10651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1820, c_10646])).
% 9.90/3.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.90/3.90  
% 9.90/3.90  Inference rules
% 9.90/3.90  ----------------------
% 9.90/3.90  #Ref     : 0
% 9.90/3.90  #Sup     : 2125
% 9.90/3.90  #Fact    : 0
% 9.90/3.90  #Define  : 0
% 9.90/3.90  #Split   : 41
% 9.90/3.90  #Chain   : 0
% 9.90/3.90  #Close   : 0
% 9.90/3.90  
% 9.90/3.90  Ordering : KBO
% 9.90/3.90  
% 9.90/3.90  Simplification rules
% 9.90/3.90  ----------------------
% 9.90/3.90  #Subsume      : 201
% 9.90/3.90  #Demod        : 4389
% 9.90/3.90  #Tautology    : 615
% 9.90/3.90  #SimpNegUnit  : 262
% 9.90/3.90  #BackRed      : 78
% 9.90/3.90  
% 9.90/3.90  #Partial instantiations: 0
% 9.90/3.90  #Strategies tried      : 1
% 9.90/3.90  
% 9.90/3.90  Timing (in seconds)
% 9.90/3.90  ----------------------
% 9.90/3.90  Preprocessing        : 0.38
% 9.90/3.90  Parsing              : 0.20
% 9.90/3.90  CNF conversion       : 0.02
% 9.90/3.90  Main loop            : 2.75
% 9.90/3.90  Inferencing          : 0.69
% 9.90/3.90  Reduction            : 1.40
% 9.90/3.90  Demodulation         : 1.14
% 9.90/3.90  BG Simplification    : 0.07
% 9.90/3.90  Subsumption          : 0.45
% 9.90/3.90  Abstraction          : 0.11
% 9.90/3.90  MUC search           : 0.00
% 9.90/3.90  Cooper               : 0.00
% 9.90/3.90  Total                : 3.19
% 9.90/3.90  Index Insertion      : 0.00
% 9.90/3.90  Index Deletion       : 0.00
% 9.90/3.91  Index Matching       : 0.00
% 9.90/3.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
