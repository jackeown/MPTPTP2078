%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:10 EST 2020

% Result     : Theorem 7.03s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 724 expanded)
%              Number of leaves         :   46 ( 275 expanded)
%              Depth                    :   11
%              Number of atoms          :  473 (2448 expanded)
%              Number of equality atoms :   97 ( 266 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_62,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_179,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_159,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(c_48,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_20,plain,(
    ! [A_10] : v2_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_71,plain,(
    ! [A_10] : v2_funct_1(k6_partfun1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4811,plain,(
    ! [B_598,E_594,D_597,C_595,F_596,A_593] :
      ( k1_partfun1(A_593,B_598,C_595,D_597,E_594,F_596) = k5_relat_1(E_594,F_596)
      | ~ m1_subset_1(F_596,k1_zfmisc_1(k2_zfmisc_1(C_595,D_597)))
      | ~ v1_funct_1(F_596)
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(A_593,B_598)))
      | ~ v1_funct_1(E_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4815,plain,(
    ! [A_593,B_598,E_594] :
      ( k1_partfun1(A_593,B_598,'#skF_2','#skF_1',E_594,'#skF_4') = k5_relat_1(E_594,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(A_593,B_598)))
      | ~ v1_funct_1(E_594) ) ),
    inference(resolution,[status(thm)],[c_60,c_4811])).

tff(c_4911,plain,(
    ! [A_603,B_604,E_605] :
      ( k1_partfun1(A_603,B_604,'#skF_2','#skF_1',E_605,'#skF_4') = k5_relat_1(E_605,'#skF_4')
      | ~ m1_subset_1(E_605,k1_zfmisc_1(k2_zfmisc_1(A_603,B_604)))
      | ~ v1_funct_1(E_605) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4815])).

tff(c_4920,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_4911])).

tff(c_4927,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4920])).

tff(c_4989,plain,(
    ! [F_609,E_611,C_610,B_607,A_608,D_606] :
      ( m1_subset_1(k1_partfun1(A_608,B_607,C_610,D_606,E_611,F_609),k1_zfmisc_1(k2_zfmisc_1(A_608,D_606)))
      | ~ m1_subset_1(F_609,k1_zfmisc_1(k2_zfmisc_1(C_610,D_606)))
      | ~ v1_funct_1(F_609)
      | ~ m1_subset_1(E_611,k1_zfmisc_1(k2_zfmisc_1(A_608,B_607)))
      | ~ v1_funct_1(E_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5019,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4927,c_4989])).

tff(c_5034,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_5019])).

tff(c_44,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4665,plain,(
    ! [D_570,C_571,A_572,B_573] :
      ( D_570 = C_571
      | ~ r2_relset_1(A_572,B_573,C_571,D_570)
      | ~ m1_subset_1(D_570,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573)))
      | ~ m1_subset_1(C_571,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4673,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_4665])).

tff(c_4688,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4673])).

tff(c_5314,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5034,c_4927,c_4927,c_4688])).

tff(c_56,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_86,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_89,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_89])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_554,plain,(
    ! [A_134,B_133,F_135,C_136,E_137,D_132] :
      ( m1_subset_1(k1_partfun1(A_134,B_133,C_136,D_132,E_137,F_135),k1_zfmisc_1(k2_zfmisc_1(A_134,D_132)))
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_136,D_132)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_314,plain,(
    ! [D_95,C_96,A_97,B_98] :
      ( D_95 = C_96
      | ~ r2_relset_1(A_97,B_98,C_96,D_95)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_322,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_314])).

tff(c_337,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_322])).

tff(c_466,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_570,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_554,c_466])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_570])).

tff(c_597,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_1436,plain,(
    ! [D_220,E_219,A_218,C_221,B_217] :
      ( k1_xboole_0 = C_221
      | v2_funct_1(D_220)
      | ~ v2_funct_1(k1_partfun1(A_218,B_217,B_217,C_221,D_220,E_219))
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(B_217,C_221)))
      | ~ v1_funct_2(E_219,B_217,C_221)
      | ~ v1_funct_1(E_219)
      | ~ m1_subset_1(D_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_217)))
      | ~ v1_funct_2(D_220,A_218,B_217)
      | ~ v1_funct_1(D_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1440,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_1436])).

tff(c_1444,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_71,c_1440])).

tff(c_1445,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1444])).

tff(c_16,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) = k1_xboole_0
      | k1_relat_1(A_6) != k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_16])).

tff(c_115,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_117,plain,(
    ! [A_63] :
      ( k1_relat_1(A_63) = k1_xboole_0
      | k2_relat_1(A_63) != k1_xboole_0
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_117])).

tff(c_133,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_126])).

tff(c_1460,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_133])).

tff(c_282,plain,(
    ! [A_88,B_89,D_90] :
      ( r2_relset_1(A_88,B_89,D_90,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_289,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_44,c_282])).

tff(c_292,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_303,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_292])).

tff(c_1547,plain,(
    ! [A_224,B_225,C_226,D_227] :
      ( k2_relset_1(A_224,B_225,C_226) = B_225
      | ~ r2_relset_1(B_225,B_225,k1_partfun1(B_225,A_224,A_224,B_225,D_227,C_226),k6_partfun1(B_225))
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(B_225,A_224)))
      | ~ v1_funct_2(D_227,B_225,A_224)
      | ~ v1_funct_1(D_227)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_2(C_226,A_224,B_225)
      | ~ v1_funct_1(C_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1553,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_1547])).

tff(c_1557,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_289,c_303,c_1553])).

tff(c_1559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1460,c_1557])).

tff(c_1560,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_1710,plain,(
    ! [C_245,B_246,A_247] :
      ( v5_relat_1(C_245,B_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1721,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1710])).

tff(c_3139,plain,(
    ! [B_407,A_408] :
      ( k2_relat_1(B_407) = A_408
      | ~ v2_funct_2(B_407,A_408)
      | ~ v5_relat_1(B_407,A_408)
      | ~ v1_relat_1(B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3151,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1721,c_3139])).

tff(c_3163,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1560,c_3151])).

tff(c_3164,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3163])).

tff(c_3458,plain,(
    ! [F_449,B_451,E_447,C_448,D_450,A_446] :
      ( k1_partfun1(A_446,B_451,C_448,D_450,E_447,F_449) = k5_relat_1(E_447,F_449)
      | ~ m1_subset_1(F_449,k1_zfmisc_1(k2_zfmisc_1(C_448,D_450)))
      | ~ v1_funct_1(F_449)
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(A_446,B_451)))
      | ~ v1_funct_1(E_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3462,plain,(
    ! [A_446,B_451,E_447] :
      ( k1_partfun1(A_446,B_451,'#skF_2','#skF_1',E_447,'#skF_4') = k5_relat_1(E_447,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_447,k1_zfmisc_1(k2_zfmisc_1(A_446,B_451)))
      | ~ v1_funct_1(E_447) ) ),
    inference(resolution,[status(thm)],[c_60,c_3458])).

tff(c_3473,plain,(
    ! [A_453,B_454,E_455] :
      ( k1_partfun1(A_453,B_454,'#skF_2','#skF_1',E_455,'#skF_4') = k5_relat_1(E_455,'#skF_4')
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(A_453,B_454)))
      | ~ v1_funct_1(E_455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3462])).

tff(c_3482,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3473])).

tff(c_3489,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3482])).

tff(c_3240,plain,(
    ! [D_421,C_422,A_423,B_424] :
      ( D_421 = C_422
      | ~ r2_relset_1(A_423,B_424,C_422,D_421)
      | ~ m1_subset_1(D_421,k1_zfmisc_1(k2_zfmisc_1(A_423,B_424)))
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_423,B_424))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3248,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_3240])).

tff(c_3263,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3248])).

tff(c_3328,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3263])).

tff(c_3496,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3489,c_3328])).

tff(c_3507,plain,(
    ! [F_459,B_457,C_460,D_456,A_458,E_461] :
      ( m1_subset_1(k1_partfun1(A_458,B_457,C_460,D_456,E_461,F_459),k1_zfmisc_1(k2_zfmisc_1(A_458,D_456)))
      | ~ m1_subset_1(F_459,k1_zfmisc_1(k2_zfmisc_1(C_460,D_456)))
      | ~ v1_funct_1(F_459)
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(A_458,B_457)))
      | ~ v1_funct_1(E_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3537,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_3507])).

tff(c_3552,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_3537])).

tff(c_3555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3496,c_3552])).

tff(c_3556,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3263])).

tff(c_4050,plain,(
    ! [C_507,A_504,B_503,E_505,D_506] :
      ( k1_xboole_0 = C_507
      | v2_funct_1(D_506)
      | ~ v2_funct_1(k1_partfun1(A_504,B_503,B_503,C_507,D_506,E_505))
      | ~ m1_subset_1(E_505,k1_zfmisc_1(k2_zfmisc_1(B_503,C_507)))
      | ~ v1_funct_2(E_505,B_503,C_507)
      | ~ v1_funct_1(E_505)
      | ~ m1_subset_1(D_506,k1_zfmisc_1(k2_zfmisc_1(A_504,B_503)))
      | ~ v1_funct_2(D_506,A_504,B_503)
      | ~ v1_funct_1(D_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4056,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3556,c_4050])).

tff(c_4062,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_71,c_4056])).

tff(c_4063,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4062])).

tff(c_2073,plain,(
    ! [E_296,C_297,D_299,A_295,B_300,F_298] :
      ( k1_partfun1(A_295,B_300,C_297,D_299,E_296,F_298) = k5_relat_1(E_296,F_298)
      | ~ m1_subset_1(F_298,k1_zfmisc_1(k2_zfmisc_1(C_297,D_299)))
      | ~ v1_funct_1(F_298)
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(A_295,B_300)))
      | ~ v1_funct_1(E_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2077,plain,(
    ! [A_295,B_300,E_296] :
      ( k1_partfun1(A_295,B_300,'#skF_2','#skF_1',E_296,'#skF_4') = k5_relat_1(E_296,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(A_295,B_300)))
      | ~ v1_funct_1(E_296) ) ),
    inference(resolution,[status(thm)],[c_60,c_2073])).

tff(c_2090,plain,(
    ! [A_305,B_306,E_307] :
      ( k1_partfun1(A_305,B_306,'#skF_2','#skF_1',E_307,'#skF_4') = k5_relat_1(E_307,'#skF_4')
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | ~ v1_funct_1(E_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2077])).

tff(c_2099,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2090])).

tff(c_2106,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2099])).

tff(c_1795,plain,(
    ! [D_261,C_262,A_263,B_264] :
      ( D_261 = C_262
      | ~ r2_relset_1(A_263,B_264,C_262,D_261)
      | ~ m1_subset_1(D_261,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264)))
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1803,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_1795])).

tff(c_1818,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1803])).

tff(c_1859,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1818])).

tff(c_2113,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_1859])).

tff(c_2124,plain,(
    ! [C_312,F_311,D_308,E_313,B_309,A_310] :
      ( m1_subset_1(k1_partfun1(A_310,B_309,C_312,D_308,E_313,F_311),k1_zfmisc_1(k2_zfmisc_1(A_310,D_308)))
      | ~ m1_subset_1(F_311,k1_zfmisc_1(k2_zfmisc_1(C_312,D_308)))
      | ~ v1_funct_1(F_311)
      | ~ m1_subset_1(E_313,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309)))
      | ~ v1_funct_1(E_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2156,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2106,c_2124])).

tff(c_2172,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_2156])).

tff(c_2175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2113,c_2172])).

tff(c_2176,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1818])).

tff(c_3099,plain,(
    ! [D_405,C_406,B_402,A_403,E_404] :
      ( k1_xboole_0 = C_406
      | v2_funct_1(D_405)
      | ~ v2_funct_1(k1_partfun1(A_403,B_402,B_402,C_406,D_405,E_404))
      | ~ m1_subset_1(E_404,k1_zfmisc_1(k2_zfmisc_1(B_402,C_406)))
      | ~ v1_funct_2(E_404,B_402,C_406)
      | ~ v1_funct_1(E_404)
      | ~ m1_subset_1(D_405,k1_zfmisc_1(k2_zfmisc_1(A_403,B_402)))
      | ~ v1_funct_2(D_405,A_403,B_402)
      | ~ v1_funct_1(D_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3103,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2176,c_3099])).

tff(c_3107,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_71,c_3103])).

tff(c_3108,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3107])).

tff(c_1724,plain,(
    ! [B_249] :
      ( v2_funct_2(B_249,k2_relat_1(B_249))
      | ~ v5_relat_1(B_249,k2_relat_1(B_249))
      | ~ v1_relat_1(B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1730,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1560,c_1724])).

tff(c_1734,plain,
    ( v2_funct_2('#skF_4',k1_xboole_0)
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1560,c_1730])).

tff(c_1743,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1734])).

tff(c_3119,plain,(
    ~ v5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3108,c_1743])).

tff(c_3136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_3119])).

tff(c_3137,plain,(
    v2_funct_2('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1734])).

tff(c_4073,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4063,c_3137])).

tff(c_4089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3164,c_4073])).

tff(c_4090,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3163])).

tff(c_109,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_16])).

tff(c_1570,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_4102,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4090,c_1570])).

tff(c_1643,plain,(
    ! [C_238,A_239,B_240] :
      ( v4_relat_1(C_238,A_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1656,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1643])).

tff(c_1658,plain,(
    ! [B_242,A_243] :
      ( r1_tarski(k1_relat_1(B_242),A_243)
      | ~ v4_relat_1(B_242,A_243)
      | ~ v1_relat_1(B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1588,plain,(
    ! [B_229,A_230] :
      ( B_229 = A_230
      | ~ r1_tarski(B_229,A_230)
      | ~ r1_tarski(A_230,B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1597,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1588])).

tff(c_1672,plain,(
    ! [B_242] :
      ( k1_relat_1(B_242) = k1_xboole_0
      | ~ v4_relat_1(B_242,k1_xboole_0)
      | ~ v1_relat_1(B_242) ) ),
    inference(resolution,[status(thm)],[c_1658,c_1597])).

tff(c_4325,plain,(
    ! [B_530] :
      ( k1_relat_1(B_530) = '#skF_1'
      | ~ v4_relat_1(B_530,'#skF_1')
      | ~ v1_relat_1(B_530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4090,c_4090,c_1672])).

tff(c_4336,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1656,c_4325])).

tff(c_4349,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_4336])).

tff(c_4351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4102,c_4349])).

tff(c_4352,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_1561,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_4620,plain,(
    ! [B_564,A_565] :
      ( v2_funct_1(B_564)
      | ~ r1_tarski(k2_relat_1(B_564),k1_relat_1(A_565))
      | ~ v2_funct_1(k5_relat_1(B_564,A_565))
      | ~ v1_funct_1(B_564)
      | ~ v1_relat_1(B_564)
      | ~ v1_funct_1(A_565)
      | ~ v1_relat_1(A_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4635,plain,(
    ! [B_564] :
      ( v2_funct_1(B_564)
      | ~ r1_tarski(k2_relat_1(B_564),k1_xboole_0)
      | ~ v2_funct_1(k5_relat_1(B_564,'#skF_4'))
      | ~ v1_funct_1(B_564)
      | ~ v1_relat_1(B_564)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_4620])).

tff(c_4743,plain,(
    ! [B_578] :
      ( v2_funct_1(B_578)
      | ~ r1_tarski(k2_relat_1(B_578),k1_xboole_0)
      | ~ v2_funct_1(k5_relat_1(B_578,'#skF_4'))
      | ~ v1_funct_1(B_578)
      | ~ v1_relat_1(B_578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_64,c_4635])).

tff(c_4749,plain,
    ( v2_funct_1('#skF_3')
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4352,c_4743])).

tff(c_4756,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_70,c_6,c_4749])).

tff(c_4757,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4756])).

tff(c_5323,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5314,c_4757])).

tff(c_5332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_5323])).

tff(c_5333,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5361,plain,(
    ! [C_630,A_631,B_632] :
      ( v1_relat_1(C_630)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5372,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5361])).

tff(c_5437,plain,(
    ! [C_641,B_642,A_643] :
      ( v5_relat_1(C_641,B_642)
      | ~ m1_subset_1(C_641,k1_zfmisc_1(k2_zfmisc_1(A_643,B_642))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5448,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_5437])).

tff(c_5527,plain,(
    ! [A_655,B_656,D_657] :
      ( r2_relset_1(A_655,B_656,D_657,D_657)
      | ~ m1_subset_1(D_657,k1_zfmisc_1(k2_zfmisc_1(A_655,B_656))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5534,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_44,c_5527])).

tff(c_5538,plain,(
    ! [A_659,B_660,C_661] :
      ( k2_relset_1(A_659,B_660,C_661) = k2_relat_1(C_661)
      | ~ m1_subset_1(C_661,k1_zfmisc_1(k2_zfmisc_1(A_659,B_660))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5549,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_5538])).

tff(c_5799,plain,(
    ! [B_700,A_701,C_703,F_702,E_704,D_699] :
      ( m1_subset_1(k1_partfun1(A_701,B_700,C_703,D_699,E_704,F_702),k1_zfmisc_1(k2_zfmisc_1(A_701,D_699)))
      | ~ m1_subset_1(F_702,k1_zfmisc_1(k2_zfmisc_1(C_703,D_699)))
      | ~ v1_funct_1(F_702)
      | ~ m1_subset_1(E_704,k1_zfmisc_1(k2_zfmisc_1(A_701,B_700)))
      | ~ v1_funct_1(E_704) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5568,plain,(
    ! [D_663,C_664,A_665,B_666] :
      ( D_663 = C_664
      | ~ r2_relset_1(A_665,B_666,C_664,D_663)
      | ~ m1_subset_1(D_663,k1_zfmisc_1(k2_zfmisc_1(A_665,B_666)))
      | ~ m1_subset_1(C_664,k1_zfmisc_1(k2_zfmisc_1(A_665,B_666))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5576,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_5568])).

tff(c_5591,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5576])).

tff(c_5712,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5591])).

tff(c_5815,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5799,c_5712])).

tff(c_5841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_5815])).

tff(c_5842,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5591])).

tff(c_6349,plain,(
    ! [A_747,B_748,C_749,D_750] :
      ( k2_relset_1(A_747,B_748,C_749) = B_748
      | ~ r2_relset_1(B_748,B_748,k1_partfun1(B_748,A_747,A_747,B_748,D_750,C_749),k6_partfun1(B_748))
      | ~ m1_subset_1(D_750,k1_zfmisc_1(k2_zfmisc_1(B_748,A_747)))
      | ~ v1_funct_2(D_750,B_748,A_747)
      | ~ v1_funct_1(D_750)
      | ~ m1_subset_1(C_749,k1_zfmisc_1(k2_zfmisc_1(A_747,B_748)))
      | ~ v1_funct_2(C_749,A_747,B_748)
      | ~ v1_funct_1(C_749) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6355,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5842,c_6349])).

tff(c_6359,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_5534,c_5549,c_6355])).

tff(c_34,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6368,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6359,c_34])).

tff(c_6374,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5372,c_5448,c_6359,c_6368])).

tff(c_6376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5333,c_6374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.03/2.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.03/2.44  
% 7.03/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.03/2.44  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.03/2.44  
% 7.03/2.44  %Foreground sorts:
% 7.03/2.44  
% 7.03/2.44  
% 7.03/2.44  %Background operators:
% 7.03/2.44  
% 7.03/2.44  
% 7.03/2.44  %Foreground operators:
% 7.03/2.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.03/2.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.03/2.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.03/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.03/2.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.03/2.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.03/2.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.03/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.03/2.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.03/2.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.03/2.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.03/2.44  tff('#skF_2', type, '#skF_2': $i).
% 7.03/2.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.03/2.44  tff('#skF_3', type, '#skF_3': $i).
% 7.03/2.44  tff('#skF_1', type, '#skF_1': $i).
% 7.03/2.44  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.03/2.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.03/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.03/2.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.03/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.03/2.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.03/2.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.03/2.44  tff('#skF_4', type, '#skF_4': $i).
% 7.03/2.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.03/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.03/2.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.03/2.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.03/2.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.03/2.44  
% 7.29/2.47  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.29/2.47  tff(f_62, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 7.29/2.47  tff(f_179, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 7.29/2.47  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.29/2.47  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.29/2.47  tff(f_108, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.29/2.47  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.29/2.47  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.29/2.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.29/2.47  tff(f_159, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 7.29/2.47  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 7.29/2.47  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.29/2.47  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.29/2.47  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.29/2.47  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.29/2.47  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.29/2.47  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.29/2.47  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 7.29/2.47  tff(c_48, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.29/2.47  tff(c_20, plain, (![A_10]: (v2_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.29/2.47  tff(c_71, plain, (![A_10]: (v2_funct_1(k6_partfun1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 7.29/2.47  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.29/2.47  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.29/2.47  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.29/2.47  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.29/2.47  tff(c_4811, plain, (![B_598, E_594, D_597, C_595, F_596, A_593]: (k1_partfun1(A_593, B_598, C_595, D_597, E_594, F_596)=k5_relat_1(E_594, F_596) | ~m1_subset_1(F_596, k1_zfmisc_1(k2_zfmisc_1(C_595, D_597))) | ~v1_funct_1(F_596) | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(A_593, B_598))) | ~v1_funct_1(E_594))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.29/2.47  tff(c_4815, plain, (![A_593, B_598, E_594]: (k1_partfun1(A_593, B_598, '#skF_2', '#skF_1', E_594, '#skF_4')=k5_relat_1(E_594, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(A_593, B_598))) | ~v1_funct_1(E_594))), inference(resolution, [status(thm)], [c_60, c_4811])).
% 7.29/2.47  tff(c_4911, plain, (![A_603, B_604, E_605]: (k1_partfun1(A_603, B_604, '#skF_2', '#skF_1', E_605, '#skF_4')=k5_relat_1(E_605, '#skF_4') | ~m1_subset_1(E_605, k1_zfmisc_1(k2_zfmisc_1(A_603, B_604))) | ~v1_funct_1(E_605))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4815])).
% 7.29/2.47  tff(c_4920, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_4911])).
% 7.29/2.47  tff(c_4927, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4920])).
% 7.29/2.47  tff(c_4989, plain, (![F_609, E_611, C_610, B_607, A_608, D_606]: (m1_subset_1(k1_partfun1(A_608, B_607, C_610, D_606, E_611, F_609), k1_zfmisc_1(k2_zfmisc_1(A_608, D_606))) | ~m1_subset_1(F_609, k1_zfmisc_1(k2_zfmisc_1(C_610, D_606))) | ~v1_funct_1(F_609) | ~m1_subset_1(E_611, k1_zfmisc_1(k2_zfmisc_1(A_608, B_607))) | ~v1_funct_1(E_611))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.29/2.47  tff(c_5019, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4927, c_4989])).
% 7.29/2.47  tff(c_5034, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_5019])).
% 7.29/2.47  tff(c_44, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.29/2.47  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.29/2.47  tff(c_4665, plain, (![D_570, C_571, A_572, B_573]: (D_570=C_571 | ~r2_relset_1(A_572, B_573, C_571, D_570) | ~m1_subset_1(D_570, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))) | ~m1_subset_1(C_571, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.29/2.47  tff(c_4673, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_4665])).
% 7.29/2.47  tff(c_4688, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4673])).
% 7.29/2.47  tff(c_5314, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5034, c_4927, c_4927, c_4688])).
% 7.29/2.47  tff(c_56, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.29/2.47  tff(c_86, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 7.29/2.47  tff(c_89, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.29/2.47  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_89])).
% 7.29/2.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.29/2.47  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_89])).
% 7.29/2.47  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.29/2.47  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.29/2.47  tff(c_554, plain, (![A_134, B_133, F_135, C_136, E_137, D_132]: (m1_subset_1(k1_partfun1(A_134, B_133, C_136, D_132, E_137, F_135), k1_zfmisc_1(k2_zfmisc_1(A_134, D_132))) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_136, D_132))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.29/2.47  tff(c_314, plain, (![D_95, C_96, A_97, B_98]: (D_95=C_96 | ~r2_relset_1(A_97, B_98, C_96, D_95) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.29/2.47  tff(c_322, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_314])).
% 7.29/2.47  tff(c_337, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_322])).
% 7.29/2.47  tff(c_466, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_337])).
% 7.29/2.47  tff(c_570, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_554, c_466])).
% 7.29/2.47  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_570])).
% 7.29/2.47  tff(c_597, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_337])).
% 7.29/2.47  tff(c_1436, plain, (![D_220, E_219, A_218, C_221, B_217]: (k1_xboole_0=C_221 | v2_funct_1(D_220) | ~v2_funct_1(k1_partfun1(A_218, B_217, B_217, C_221, D_220, E_219)) | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(B_217, C_221))) | ~v1_funct_2(E_219, B_217, C_221) | ~v1_funct_1(E_219) | ~m1_subset_1(D_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_217))) | ~v1_funct_2(D_220, A_218, B_217) | ~v1_funct_1(D_220))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.29/2.47  tff(c_1440, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_597, c_1436])).
% 7.29/2.47  tff(c_1444, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_71, c_1440])).
% 7.29/2.47  tff(c_1445, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_1444])).
% 7.29/2.47  tff(c_16, plain, (![A_6]: (k2_relat_1(A_6)=k1_xboole_0 | k1_relat_1(A_6)!=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.29/2.47  tff(c_105, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_16])).
% 7.29/2.47  tff(c_115, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_105])).
% 7.29/2.47  tff(c_117, plain, (![A_63]: (k1_relat_1(A_63)=k1_xboole_0 | k2_relat_1(A_63)!=k1_xboole_0 | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.29/2.47  tff(c_126, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_117])).
% 7.29/2.47  tff(c_133, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_115, c_126])).
% 7.29/2.47  tff(c_1460, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_133])).
% 7.29/2.47  tff(c_282, plain, (![A_88, B_89, D_90]: (r2_relset_1(A_88, B_89, D_90, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.29/2.47  tff(c_289, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_44, c_282])).
% 7.29/2.47  tff(c_292, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.29/2.47  tff(c_303, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_292])).
% 7.29/2.47  tff(c_1547, plain, (![A_224, B_225, C_226, D_227]: (k2_relset_1(A_224, B_225, C_226)=B_225 | ~r2_relset_1(B_225, B_225, k1_partfun1(B_225, A_224, A_224, B_225, D_227, C_226), k6_partfun1(B_225)) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(B_225, A_224))) | ~v1_funct_2(D_227, B_225, A_224) | ~v1_funct_1(D_227) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_2(C_226, A_224, B_225) | ~v1_funct_1(C_226))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.29/2.47  tff(c_1553, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_597, c_1547])).
% 7.29/2.47  tff(c_1557, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_289, c_303, c_1553])).
% 7.29/2.47  tff(c_1559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1460, c_1557])).
% 7.29/2.47  tff(c_1560, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_105])).
% 7.29/2.47  tff(c_1710, plain, (![C_245, B_246, A_247]: (v5_relat_1(C_245, B_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.29/2.47  tff(c_1721, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1710])).
% 7.29/2.47  tff(c_3139, plain, (![B_407, A_408]: (k2_relat_1(B_407)=A_408 | ~v2_funct_2(B_407, A_408) | ~v5_relat_1(B_407, A_408) | ~v1_relat_1(B_407))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.29/2.47  tff(c_3151, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1721, c_3139])).
% 7.29/2.47  tff(c_3163, plain, (k1_xboole_0='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1560, c_3151])).
% 7.29/2.47  tff(c_3164, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_3163])).
% 7.29/2.47  tff(c_3458, plain, (![F_449, B_451, E_447, C_448, D_450, A_446]: (k1_partfun1(A_446, B_451, C_448, D_450, E_447, F_449)=k5_relat_1(E_447, F_449) | ~m1_subset_1(F_449, k1_zfmisc_1(k2_zfmisc_1(C_448, D_450))) | ~v1_funct_1(F_449) | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(A_446, B_451))) | ~v1_funct_1(E_447))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.29/2.47  tff(c_3462, plain, (![A_446, B_451, E_447]: (k1_partfun1(A_446, B_451, '#skF_2', '#skF_1', E_447, '#skF_4')=k5_relat_1(E_447, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_447, k1_zfmisc_1(k2_zfmisc_1(A_446, B_451))) | ~v1_funct_1(E_447))), inference(resolution, [status(thm)], [c_60, c_3458])).
% 7.29/2.47  tff(c_3473, plain, (![A_453, B_454, E_455]: (k1_partfun1(A_453, B_454, '#skF_2', '#skF_1', E_455, '#skF_4')=k5_relat_1(E_455, '#skF_4') | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(A_453, B_454))) | ~v1_funct_1(E_455))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3462])).
% 7.29/2.47  tff(c_3482, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3473])).
% 7.29/2.47  tff(c_3489, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3482])).
% 7.29/2.47  tff(c_3240, plain, (![D_421, C_422, A_423, B_424]: (D_421=C_422 | ~r2_relset_1(A_423, B_424, C_422, D_421) | ~m1_subset_1(D_421, k1_zfmisc_1(k2_zfmisc_1(A_423, B_424))) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_423, B_424))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.29/2.47  tff(c_3248, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_3240])).
% 7.29/2.47  tff(c_3263, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3248])).
% 7.29/2.47  tff(c_3328, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3263])).
% 7.29/2.47  tff(c_3496, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3489, c_3328])).
% 7.29/2.47  tff(c_3507, plain, (![F_459, B_457, C_460, D_456, A_458, E_461]: (m1_subset_1(k1_partfun1(A_458, B_457, C_460, D_456, E_461, F_459), k1_zfmisc_1(k2_zfmisc_1(A_458, D_456))) | ~m1_subset_1(F_459, k1_zfmisc_1(k2_zfmisc_1(C_460, D_456))) | ~v1_funct_1(F_459) | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(A_458, B_457))) | ~v1_funct_1(E_461))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.29/2.47  tff(c_3537, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3489, c_3507])).
% 7.29/2.47  tff(c_3552, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_3537])).
% 7.29/2.47  tff(c_3555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3496, c_3552])).
% 7.29/2.47  tff(c_3556, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3263])).
% 7.29/2.47  tff(c_4050, plain, (![C_507, A_504, B_503, E_505, D_506]: (k1_xboole_0=C_507 | v2_funct_1(D_506) | ~v2_funct_1(k1_partfun1(A_504, B_503, B_503, C_507, D_506, E_505)) | ~m1_subset_1(E_505, k1_zfmisc_1(k2_zfmisc_1(B_503, C_507))) | ~v1_funct_2(E_505, B_503, C_507) | ~v1_funct_1(E_505) | ~m1_subset_1(D_506, k1_zfmisc_1(k2_zfmisc_1(A_504, B_503))) | ~v1_funct_2(D_506, A_504, B_503) | ~v1_funct_1(D_506))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.29/2.47  tff(c_4056, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3556, c_4050])).
% 7.29/2.47  tff(c_4062, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_71, c_4056])).
% 7.29/2.47  tff(c_4063, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_4062])).
% 7.29/2.47  tff(c_2073, plain, (![E_296, C_297, D_299, A_295, B_300, F_298]: (k1_partfun1(A_295, B_300, C_297, D_299, E_296, F_298)=k5_relat_1(E_296, F_298) | ~m1_subset_1(F_298, k1_zfmisc_1(k2_zfmisc_1(C_297, D_299))) | ~v1_funct_1(F_298) | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(A_295, B_300))) | ~v1_funct_1(E_296))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.29/2.47  tff(c_2077, plain, (![A_295, B_300, E_296]: (k1_partfun1(A_295, B_300, '#skF_2', '#skF_1', E_296, '#skF_4')=k5_relat_1(E_296, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(A_295, B_300))) | ~v1_funct_1(E_296))), inference(resolution, [status(thm)], [c_60, c_2073])).
% 7.29/2.47  tff(c_2090, plain, (![A_305, B_306, E_307]: (k1_partfun1(A_305, B_306, '#skF_2', '#skF_1', E_307, '#skF_4')=k5_relat_1(E_307, '#skF_4') | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | ~v1_funct_1(E_307))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2077])).
% 7.29/2.47  tff(c_2099, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2090])).
% 7.29/2.47  tff(c_2106, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2099])).
% 7.29/2.47  tff(c_1795, plain, (![D_261, C_262, A_263, B_264]: (D_261=C_262 | ~r2_relset_1(A_263, B_264, C_262, D_261) | ~m1_subset_1(D_261, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.29/2.47  tff(c_1803, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_1795])).
% 7.29/2.47  tff(c_1818, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1803])).
% 7.29/2.47  tff(c_1859, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1818])).
% 7.29/2.47  tff(c_2113, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_1859])).
% 7.29/2.47  tff(c_2124, plain, (![C_312, F_311, D_308, E_313, B_309, A_310]: (m1_subset_1(k1_partfun1(A_310, B_309, C_312, D_308, E_313, F_311), k1_zfmisc_1(k2_zfmisc_1(A_310, D_308))) | ~m1_subset_1(F_311, k1_zfmisc_1(k2_zfmisc_1(C_312, D_308))) | ~v1_funct_1(F_311) | ~m1_subset_1(E_313, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))) | ~v1_funct_1(E_313))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.29/2.48  tff(c_2156, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2106, c_2124])).
% 7.29/2.48  tff(c_2172, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_2156])).
% 7.29/2.48  tff(c_2175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2113, c_2172])).
% 7.29/2.48  tff(c_2176, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1818])).
% 7.29/2.48  tff(c_3099, plain, (![D_405, C_406, B_402, A_403, E_404]: (k1_xboole_0=C_406 | v2_funct_1(D_405) | ~v2_funct_1(k1_partfun1(A_403, B_402, B_402, C_406, D_405, E_404)) | ~m1_subset_1(E_404, k1_zfmisc_1(k2_zfmisc_1(B_402, C_406))) | ~v1_funct_2(E_404, B_402, C_406) | ~v1_funct_1(E_404) | ~m1_subset_1(D_405, k1_zfmisc_1(k2_zfmisc_1(A_403, B_402))) | ~v1_funct_2(D_405, A_403, B_402) | ~v1_funct_1(D_405))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.29/2.48  tff(c_3103, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2176, c_3099])).
% 7.29/2.48  tff(c_3107, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_71, c_3103])).
% 7.29/2.48  tff(c_3108, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_3107])).
% 7.29/2.48  tff(c_1724, plain, (![B_249]: (v2_funct_2(B_249, k2_relat_1(B_249)) | ~v5_relat_1(B_249, k2_relat_1(B_249)) | ~v1_relat_1(B_249))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.29/2.48  tff(c_1730, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1560, c_1724])).
% 7.29/2.48  tff(c_1734, plain, (v2_funct_2('#skF_4', k1_xboole_0) | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1560, c_1730])).
% 7.29/2.48  tff(c_1743, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1734])).
% 7.29/2.48  tff(c_3119, plain, (~v5_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3108, c_1743])).
% 7.29/2.48  tff(c_3136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1721, c_3119])).
% 7.29/2.48  tff(c_3137, plain, (v2_funct_2('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1734])).
% 7.29/2.48  tff(c_4073, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4063, c_3137])).
% 7.29/2.48  tff(c_4089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3164, c_4073])).
% 7.29/2.48  tff(c_4090, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3163])).
% 7.29/2.48  tff(c_109, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_16])).
% 7.29/2.48  tff(c_1570, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_109])).
% 7.29/2.48  tff(c_4102, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4090, c_1570])).
% 7.29/2.48  tff(c_1643, plain, (![C_238, A_239, B_240]: (v4_relat_1(C_238, A_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.29/2.48  tff(c_1656, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_1643])).
% 7.29/2.48  tff(c_1658, plain, (![B_242, A_243]: (r1_tarski(k1_relat_1(B_242), A_243) | ~v4_relat_1(B_242, A_243) | ~v1_relat_1(B_242))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.29/2.48  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.29/2.48  tff(c_1588, plain, (![B_229, A_230]: (B_229=A_230 | ~r1_tarski(B_229, A_230) | ~r1_tarski(A_230, B_229))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.29/2.48  tff(c_1597, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1588])).
% 7.29/2.48  tff(c_1672, plain, (![B_242]: (k1_relat_1(B_242)=k1_xboole_0 | ~v4_relat_1(B_242, k1_xboole_0) | ~v1_relat_1(B_242))), inference(resolution, [status(thm)], [c_1658, c_1597])).
% 7.29/2.48  tff(c_4325, plain, (![B_530]: (k1_relat_1(B_530)='#skF_1' | ~v4_relat_1(B_530, '#skF_1') | ~v1_relat_1(B_530))), inference(demodulation, [status(thm), theory('equality')], [c_4090, c_4090, c_1672])).
% 7.29/2.48  tff(c_4336, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1656, c_4325])).
% 7.29/2.48  tff(c_4349, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_4336])).
% 7.29/2.48  tff(c_4351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4102, c_4349])).
% 7.29/2.48  tff(c_4352, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_109])).
% 7.29/2.48  tff(c_1561, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_105])).
% 7.29/2.48  tff(c_4620, plain, (![B_564, A_565]: (v2_funct_1(B_564) | ~r1_tarski(k2_relat_1(B_564), k1_relat_1(A_565)) | ~v2_funct_1(k5_relat_1(B_564, A_565)) | ~v1_funct_1(B_564) | ~v1_relat_1(B_564) | ~v1_funct_1(A_565) | ~v1_relat_1(A_565))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.29/2.48  tff(c_4635, plain, (![B_564]: (v2_funct_1(B_564) | ~r1_tarski(k2_relat_1(B_564), k1_xboole_0) | ~v2_funct_1(k5_relat_1(B_564, '#skF_4')) | ~v1_funct_1(B_564) | ~v1_relat_1(B_564) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_4620])).
% 7.29/2.48  tff(c_4743, plain, (![B_578]: (v2_funct_1(B_578) | ~r1_tarski(k2_relat_1(B_578), k1_xboole_0) | ~v2_funct_1(k5_relat_1(B_578, '#skF_4')) | ~v1_funct_1(B_578) | ~v1_relat_1(B_578))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_64, c_4635])).
% 7.29/2.48  tff(c_4749, plain, (v2_funct_1('#skF_3') | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4352, c_4743])).
% 7.29/2.48  tff(c_4756, plain, (v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_70, c_6, c_4749])).
% 7.29/2.48  tff(c_4757, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_86, c_4756])).
% 7.29/2.48  tff(c_5323, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5314, c_4757])).
% 7.29/2.48  tff(c_5332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_5323])).
% 7.29/2.48  tff(c_5333, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 7.29/2.48  tff(c_5361, plain, (![C_630, A_631, B_632]: (v1_relat_1(C_630) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.29/2.48  tff(c_5372, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_5361])).
% 7.29/2.48  tff(c_5437, plain, (![C_641, B_642, A_643]: (v5_relat_1(C_641, B_642) | ~m1_subset_1(C_641, k1_zfmisc_1(k2_zfmisc_1(A_643, B_642))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.29/2.48  tff(c_5448, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_5437])).
% 7.29/2.48  tff(c_5527, plain, (![A_655, B_656, D_657]: (r2_relset_1(A_655, B_656, D_657, D_657) | ~m1_subset_1(D_657, k1_zfmisc_1(k2_zfmisc_1(A_655, B_656))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.29/2.48  tff(c_5534, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_44, c_5527])).
% 7.29/2.48  tff(c_5538, plain, (![A_659, B_660, C_661]: (k2_relset_1(A_659, B_660, C_661)=k2_relat_1(C_661) | ~m1_subset_1(C_661, k1_zfmisc_1(k2_zfmisc_1(A_659, B_660))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.29/2.48  tff(c_5549, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_5538])).
% 7.29/2.48  tff(c_5799, plain, (![B_700, A_701, C_703, F_702, E_704, D_699]: (m1_subset_1(k1_partfun1(A_701, B_700, C_703, D_699, E_704, F_702), k1_zfmisc_1(k2_zfmisc_1(A_701, D_699))) | ~m1_subset_1(F_702, k1_zfmisc_1(k2_zfmisc_1(C_703, D_699))) | ~v1_funct_1(F_702) | ~m1_subset_1(E_704, k1_zfmisc_1(k2_zfmisc_1(A_701, B_700))) | ~v1_funct_1(E_704))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.29/2.48  tff(c_5568, plain, (![D_663, C_664, A_665, B_666]: (D_663=C_664 | ~r2_relset_1(A_665, B_666, C_664, D_663) | ~m1_subset_1(D_663, k1_zfmisc_1(k2_zfmisc_1(A_665, B_666))) | ~m1_subset_1(C_664, k1_zfmisc_1(k2_zfmisc_1(A_665, B_666))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.29/2.48  tff(c_5576, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_5568])).
% 7.29/2.48  tff(c_5591, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5576])).
% 7.29/2.48  tff(c_5712, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5591])).
% 7.29/2.48  tff(c_5815, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5799, c_5712])).
% 7.29/2.48  tff(c_5841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_5815])).
% 7.29/2.48  tff(c_5842, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5591])).
% 7.29/2.48  tff(c_6349, plain, (![A_747, B_748, C_749, D_750]: (k2_relset_1(A_747, B_748, C_749)=B_748 | ~r2_relset_1(B_748, B_748, k1_partfun1(B_748, A_747, A_747, B_748, D_750, C_749), k6_partfun1(B_748)) | ~m1_subset_1(D_750, k1_zfmisc_1(k2_zfmisc_1(B_748, A_747))) | ~v1_funct_2(D_750, B_748, A_747) | ~v1_funct_1(D_750) | ~m1_subset_1(C_749, k1_zfmisc_1(k2_zfmisc_1(A_747, B_748))) | ~v1_funct_2(C_749, A_747, B_748) | ~v1_funct_1(C_749))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.29/2.48  tff(c_6355, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5842, c_6349])).
% 7.29/2.48  tff(c_6359, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_5534, c_5549, c_6355])).
% 7.29/2.48  tff(c_34, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.29/2.48  tff(c_6368, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6359, c_34])).
% 7.29/2.48  tff(c_6374, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5372, c_5448, c_6359, c_6368])).
% 7.29/2.48  tff(c_6376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5333, c_6374])).
% 7.29/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.48  
% 7.29/2.48  Inference rules
% 7.29/2.48  ----------------------
% 7.29/2.48  #Ref     : 0
% 7.29/2.48  #Sup     : 1287
% 7.29/2.48  #Fact    : 0
% 7.29/2.48  #Define  : 0
% 7.29/2.48  #Split   : 40
% 7.29/2.48  #Chain   : 0
% 7.29/2.48  #Close   : 0
% 7.29/2.48  
% 7.29/2.48  Ordering : KBO
% 7.29/2.48  
% 7.29/2.48  Simplification rules
% 7.29/2.48  ----------------------
% 7.29/2.48  #Subsume      : 42
% 7.29/2.48  #Demod        : 1494
% 7.29/2.48  #Tautology    : 396
% 7.29/2.48  #SimpNegUnit  : 22
% 7.29/2.48  #BackRed      : 174
% 7.29/2.48  
% 7.29/2.48  #Partial instantiations: 0
% 7.29/2.48  #Strategies tried      : 1
% 7.29/2.48  
% 7.29/2.48  Timing (in seconds)
% 7.29/2.48  ----------------------
% 7.29/2.48  Preprocessing        : 0.35
% 7.29/2.48  Parsing              : 0.19
% 7.29/2.48  CNF conversion       : 0.02
% 7.29/2.48  Main loop            : 1.33
% 7.29/2.48  Inferencing          : 0.46
% 7.29/2.48  Reduction            : 0.49
% 7.29/2.48  Demodulation         : 0.35
% 7.29/2.48  BG Simplification    : 0.05
% 7.29/2.48  Subsumption          : 0.21
% 7.29/2.48  Abstraction          : 0.06
% 7.29/2.48  MUC search           : 0.00
% 7.29/2.48  Cooper               : 0.00
% 7.29/2.48  Total                : 1.74
% 7.29/2.48  Index Insertion      : 0.00
% 7.29/2.48  Index Deletion       : 0.00
% 7.29/2.48  Index Matching       : 0.00
% 7.29/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
