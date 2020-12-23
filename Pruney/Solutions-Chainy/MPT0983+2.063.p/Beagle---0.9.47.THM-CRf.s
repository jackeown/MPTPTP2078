%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:10 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 696 expanded)
%              Number of leaves         :   46 ( 265 expanded)
%              Depth                    :   11
%              Number of atoms          :  471 (2334 expanded)
%              Number of equality atoms :   94 ( 251 expanded)
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

tff(f_122,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_181,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_110,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_86,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_161,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(c_50,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_20,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_4821,plain,(
    ! [B_605,D_604,A_606,F_607,E_609,C_608] :
      ( m1_subset_1(k1_partfun1(A_606,B_605,C_608,D_604,E_609,F_607),k1_zfmisc_1(k2_zfmisc_1(A_606,D_604)))
      | ~ m1_subset_1(F_607,k1_zfmisc_1(k2_zfmisc_1(C_608,D_604)))
      | ~ v1_funct_1(F_607)
      | ~ m1_subset_1(E_609,k1_zfmisc_1(k2_zfmisc_1(A_606,B_605)))
      | ~ v1_funct_1(E_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_4522,plain,(
    ! [D_570,C_571,A_572,B_573] :
      ( D_570 = C_571
      | ~ r2_relset_1(A_572,B_573,C_571,D_570)
      | ~ m1_subset_1(D_570,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573)))
      | ~ m1_subset_1(C_571,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4530,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_4522])).

tff(c_4545,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4530])).

tff(c_4628,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4545])).

tff(c_4834,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4821,c_4628])).

tff(c_4856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_4834])).

tff(c_4857,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4545])).

tff(c_5026,plain,(
    ! [F_630,E_628,A_627,C_629,B_632,D_631] :
      ( k1_partfun1(A_627,B_632,C_629,D_631,E_628,F_630) = k5_relat_1(E_628,F_630)
      | ~ m1_subset_1(F_630,k1_zfmisc_1(k2_zfmisc_1(C_629,D_631)))
      | ~ v1_funct_1(F_630)
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(A_627,B_632)))
      | ~ v1_funct_1(E_628) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5030,plain,(
    ! [A_627,B_632,E_628] :
      ( k1_partfun1(A_627,B_632,'#skF_2','#skF_1',E_628,'#skF_4') = k5_relat_1(E_628,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(A_627,B_632)))
      | ~ v1_funct_1(E_628) ) ),
    inference(resolution,[status(thm)],[c_62,c_5026])).

tff(c_5059,plain,(
    ! [A_637,B_638,E_639] :
      ( k1_partfun1(A_637,B_638,'#skF_2','#skF_1',E_639,'#skF_4') = k5_relat_1(E_639,'#skF_4')
      | ~ m1_subset_1(E_639,k1_zfmisc_1(k2_zfmisc_1(A_637,B_638)))
      | ~ v1_funct_1(E_639) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5030])).

tff(c_5068,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5059])).

tff(c_5075,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4857,c_5068])).

tff(c_58,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_90,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_125,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_138,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_125])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_551,plain,(
    ! [A_134,B_133,F_135,C_136,E_137,D_132] :
      ( m1_subset_1(k1_partfun1(A_134,B_133,C_136,D_132,E_137,F_135),k1_zfmisc_1(k2_zfmisc_1(A_134,D_132)))
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_136,D_132)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_383,plain,(
    ! [D_103,C_104,A_105,B_106] :
      ( D_103 = C_104
      | ~ r2_relset_1(A_105,B_106,C_104,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_391,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_383])).

tff(c_406,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_391])).

tff(c_432,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_567,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_551,c_432])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_567])).

tff(c_591,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_1041,plain,(
    ! [E_177,A_176,D_178,B_175,C_179] :
      ( k1_xboole_0 = C_179
      | v2_funct_1(D_178)
      | ~ v2_funct_1(k1_partfun1(A_176,B_175,B_175,C_179,D_178,E_177))
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(B_175,C_179)))
      | ~ v1_funct_2(E_177,B_175,C_179)
      | ~ v1_funct_1(E_177)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_175)))
      | ~ v1_funct_2(D_178,A_176,B_175)
      | ~ v1_funct_1(D_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1045,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_1041])).

tff(c_1049,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_73,c_1045])).

tff(c_1050,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1049])).

tff(c_14,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) = k1_xboole_0
      | k2_relat_1(A_6) != k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_14])).

tff(c_155,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_1065,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_155])).

tff(c_284,plain,(
    ! [A_88,B_89,D_90] :
      ( r2_relset_1(A_88,B_89,D_90,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_291,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_46,c_284])).

tff(c_294,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_305,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_294])).

tff(c_1139,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( k2_relset_1(A_183,B_184,C_185) = B_184
      | ~ r2_relset_1(B_184,B_184,k1_partfun1(B_184,A_183,A_183,B_184,D_186,C_185),k6_partfun1(B_184))
      | ~ m1_subset_1(D_186,k1_zfmisc_1(k2_zfmisc_1(B_184,A_183)))
      | ~ v1_funct_2(D_186,B_184,A_183)
      | ~ v1_funct_1(D_186)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_2(C_185,A_183,B_184)
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1145,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_591,c_1139])).

tff(c_1149,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_291,c_305,c_1145])).

tff(c_1151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_1149])).

tff(c_1153,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_1273,plain,(
    ! [C_201,B_202,A_203] :
      ( v5_relat_1(C_201,B_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1284,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1273])).

tff(c_2575,plain,(
    ! [B_345,A_346] :
      ( k2_relat_1(B_345) = A_346
      | ~ v2_funct_2(B_345,A_346)
      | ~ v5_relat_1(B_345,A_346)
      | ~ v1_relat_1(B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2587,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1284,c_2575])).

tff(c_2599,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1153,c_2587])).

tff(c_2600,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2599])).

tff(c_3476,plain,(
    ! [A_454,F_457,C_456,D_458,E_455,B_459] :
      ( k1_partfun1(A_454,B_459,C_456,D_458,E_455,F_457) = k5_relat_1(E_455,F_457)
      | ~ m1_subset_1(F_457,k1_zfmisc_1(k2_zfmisc_1(C_456,D_458)))
      | ~ v1_funct_1(F_457)
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(A_454,B_459)))
      | ~ v1_funct_1(E_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3480,plain,(
    ! [A_454,B_459,E_455] :
      ( k1_partfun1(A_454,B_459,'#skF_2','#skF_1',E_455,'#skF_4') = k5_relat_1(E_455,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(A_454,B_459)))
      | ~ v1_funct_1(E_455) ) ),
    inference(resolution,[status(thm)],[c_62,c_3476])).

tff(c_3509,plain,(
    ! [A_465,B_466,E_467] :
      ( k1_partfun1(A_465,B_466,'#skF_2','#skF_1',E_467,'#skF_4') = k5_relat_1(E_467,'#skF_4')
      | ~ m1_subset_1(E_467,k1_zfmisc_1(k2_zfmisc_1(A_465,B_466)))
      | ~ v1_funct_1(E_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3480])).

tff(c_3518,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3509])).

tff(c_3525,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3518])).

tff(c_2779,plain,(
    ! [D_367,C_368,A_369,B_370] :
      ( D_367 = C_368
      | ~ r2_relset_1(A_369,B_370,C_368,D_367)
      | ~ m1_subset_1(D_367,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370)))
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2787,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_2779])).

tff(c_2802,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2787])).

tff(c_3444,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2802])).

tff(c_3532,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3525,c_3444])).

tff(c_3538,plain,(
    ! [A_470,F_471,C_472,B_469,D_468,E_473] :
      ( m1_subset_1(k1_partfun1(A_470,B_469,C_472,D_468,E_473,F_471),k1_zfmisc_1(k2_zfmisc_1(A_470,D_468)))
      | ~ m1_subset_1(F_471,k1_zfmisc_1(k2_zfmisc_1(C_472,D_468)))
      | ~ v1_funct_1(F_471)
      | ~ m1_subset_1(E_473,k1_zfmisc_1(k2_zfmisc_1(A_470,B_469)))
      | ~ v1_funct_1(E_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3568,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3525,c_3538])).

tff(c_3583,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_3568])).

tff(c_3612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3532,c_3583])).

tff(c_3613,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2802])).

tff(c_4003,plain,(
    ! [C_517,D_516,E_515,B_513,A_514] :
      ( k1_xboole_0 = C_517
      | v2_funct_1(D_516)
      | ~ v2_funct_1(k1_partfun1(A_514,B_513,B_513,C_517,D_516,E_515))
      | ~ m1_subset_1(E_515,k1_zfmisc_1(k2_zfmisc_1(B_513,C_517)))
      | ~ v1_funct_2(E_515,B_513,C_517)
      | ~ v1_funct_1(E_515)
      | ~ m1_subset_1(D_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_513)))
      | ~ v1_funct_2(D_516,A_514,B_513)
      | ~ v1_funct_1(D_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4007,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3613,c_4003])).

tff(c_4011,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_73,c_4007])).

tff(c_4012,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_4011])).

tff(c_1650,plain,(
    ! [B_256,F_258,A_257,C_259,D_255,E_260] :
      ( m1_subset_1(k1_partfun1(A_257,B_256,C_259,D_255,E_260,F_258),k1_zfmisc_1(k2_zfmisc_1(A_257,D_255)))
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(C_259,D_255)))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(A_257,B_256)))
      | ~ v1_funct_1(E_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1485,plain,(
    ! [D_227,C_228,A_229,B_230] :
      ( D_227 = C_228
      | ~ r2_relset_1(A_229,B_230,C_228,D_227)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1493,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_1485])).

tff(c_1508,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1493])).

tff(c_1562,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1508])).

tff(c_1666,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1650,c_1562])).

tff(c_1692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_1666])).

tff(c_1693,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1508])).

tff(c_2535,plain,(
    ! [E_342,A_341,D_343,C_344,B_340] :
      ( k1_xboole_0 = C_344
      | v2_funct_1(D_343)
      | ~ v2_funct_1(k1_partfun1(A_341,B_340,B_340,C_344,D_343,E_342))
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(B_340,C_344)))
      | ~ v1_funct_2(E_342,B_340,C_344)
      | ~ v1_funct_1(E_342)
      | ~ m1_subset_1(D_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_340)))
      | ~ v1_funct_2(D_343,A_341,B_340)
      | ~ v1_funct_1(D_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2539,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1693,c_2535])).

tff(c_2543,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_73,c_2539])).

tff(c_2544,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2543])).

tff(c_1286,plain,(
    ! [B_204] :
      ( v2_funct_2(B_204,k2_relat_1(B_204))
      | ~ v5_relat_1(B_204,k2_relat_1(B_204))
      | ~ v1_relat_1(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1292,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_1286])).

tff(c_1296,plain,
    ( v2_funct_2('#skF_4',k1_xboole_0)
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1153,c_1292])).

tff(c_1298,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_2555,plain,(
    ~ v5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2544,c_1298])).

tff(c_2572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_2555])).

tff(c_2573,plain,(
    v2_funct_2('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_4024,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4012,c_2573])).

tff(c_4041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2600,c_4024])).

tff(c_4042,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2599])).

tff(c_16,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) = k1_xboole_0
      | k1_relat_1(A_6) != k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_16])).

tff(c_1162,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_4052,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4042,c_1162])).

tff(c_1224,plain,(
    ! [C_196,A_197,B_198] :
      ( v4_relat_1(C_196,A_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1237,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1224])).

tff(c_1180,plain,(
    ! [B_189,A_190] :
      ( r1_tarski(k1_relat_1(B_189),A_190)
      | ~ v4_relat_1(B_189,A_190)
      | ~ v1_relat_1(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_1190,plain,(
    ! [B_189] :
      ( k1_relat_1(B_189) = k1_xboole_0
      | ~ v4_relat_1(B_189,k1_xboole_0)
      | ~ v1_relat_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_1180,c_106])).

tff(c_4221,plain,(
    ! [B_536] :
      ( k1_relat_1(B_536) = '#skF_1'
      | ~ v4_relat_1(B_536,'#skF_1')
      | ~ v1_relat_1(B_536) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4042,c_4042,c_1190])).

tff(c_4232,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1237,c_4221])).

tff(c_4245,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_4232])).

tff(c_4247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4052,c_4245])).

tff(c_4248,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_1152,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_4874,plain,(
    ! [B_611,A_612] :
      ( v2_funct_1(B_611)
      | ~ r1_tarski(k2_relat_1(B_611),k1_relat_1(A_612))
      | ~ v2_funct_1(k5_relat_1(B_611,A_612))
      | ~ v1_funct_1(B_611)
      | ~ v1_relat_1(B_611)
      | ~ v1_funct_1(A_612)
      | ~ v1_relat_1(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4892,plain,(
    ! [B_611] :
      ( v2_funct_1(B_611)
      | ~ r1_tarski(k2_relat_1(B_611),k1_xboole_0)
      | ~ v2_funct_1(k5_relat_1(B_611,'#skF_4'))
      | ~ v1_funct_1(B_611)
      | ~ v1_relat_1(B_611)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1152,c_4874])).

tff(c_5004,plain,(
    ! [B_626] :
      ( v2_funct_1(B_626)
      | ~ r1_tarski(k2_relat_1(B_626),k1_xboole_0)
      | ~ v2_funct_1(k5_relat_1(B_626,'#skF_4'))
      | ~ v1_funct_1(B_626)
      | ~ v1_relat_1(B_626) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_66,c_4892])).

tff(c_5013,plain,
    ( v2_funct_1('#skF_3')
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4248,c_5004])).

tff(c_5022,plain,
    ( v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_72,c_6,c_5013])).

tff(c_5023,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_5022])).

tff(c_5076,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5075,c_5023])).

tff(c_5079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_5076])).

tff(c_5080,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5116,plain,(
    ! [C_646,A_647,B_648] :
      ( v1_relat_1(C_646)
      | ~ m1_subset_1(C_646,k1_zfmisc_1(k2_zfmisc_1(A_647,B_648))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5129,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_5116])).

tff(c_5206,plain,(
    ! [C_661,B_662,A_663] :
      ( v5_relat_1(C_661,B_662)
      | ~ m1_subset_1(C_661,k1_zfmisc_1(k2_zfmisc_1(A_663,B_662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5218,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_5206])).

tff(c_5273,plain,(
    ! [A_669,B_670,D_671] :
      ( r2_relset_1(A_669,B_670,D_671,D_671)
      | ~ m1_subset_1(D_671,k1_zfmisc_1(k2_zfmisc_1(A_669,B_670))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5280,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_46,c_5273])).

tff(c_5284,plain,(
    ! [A_673,B_674,C_675] :
      ( k2_relset_1(A_673,B_674,C_675) = k2_relat_1(C_675)
      | ~ m1_subset_1(C_675,k1_zfmisc_1(k2_zfmisc_1(A_673,B_674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5296,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_5284])).

tff(c_5510,plain,(
    ! [F_708,A_705,E_706,C_707,B_710,D_709] :
      ( k1_partfun1(A_705,B_710,C_707,D_709,E_706,F_708) = k5_relat_1(E_706,F_708)
      | ~ m1_subset_1(F_708,k1_zfmisc_1(k2_zfmisc_1(C_707,D_709)))
      | ~ v1_funct_1(F_708)
      | ~ m1_subset_1(E_706,k1_zfmisc_1(k2_zfmisc_1(A_705,B_710)))
      | ~ v1_funct_1(E_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5516,plain,(
    ! [A_705,B_710,E_706] :
      ( k1_partfun1(A_705,B_710,'#skF_2','#skF_1',E_706,'#skF_4') = k5_relat_1(E_706,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_706,k1_zfmisc_1(k2_zfmisc_1(A_705,B_710)))
      | ~ v1_funct_1(E_706) ) ),
    inference(resolution,[status(thm)],[c_62,c_5510])).

tff(c_5552,plain,(
    ! [A_715,B_716,E_717] :
      ( k1_partfun1(A_715,B_716,'#skF_2','#skF_1',E_717,'#skF_4') = k5_relat_1(E_717,'#skF_4')
      | ~ m1_subset_1(E_717,k1_zfmisc_1(k2_zfmisc_1(A_715,B_716)))
      | ~ v1_funct_1(E_717) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5516])).

tff(c_5558,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5552])).

tff(c_5565,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5558])).

tff(c_5337,plain,(
    ! [D_680,C_681,A_682,B_683] :
      ( D_680 = C_681
      | ~ r2_relset_1(A_682,B_683,C_681,D_680)
      | ~ m1_subset_1(D_680,k1_zfmisc_1(k2_zfmisc_1(A_682,B_683)))
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1(A_682,B_683))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5345,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_5337])).

tff(c_5360,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5345])).

tff(c_5399,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5360])).

tff(c_5570,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5565,c_5399])).

tff(c_5576,plain,(
    ! [B_719,E_723,C_722,D_718,F_721,A_720] :
      ( m1_subset_1(k1_partfun1(A_720,B_719,C_722,D_718,E_723,F_721),k1_zfmisc_1(k2_zfmisc_1(A_720,D_718)))
      | ~ m1_subset_1(F_721,k1_zfmisc_1(k2_zfmisc_1(C_722,D_718)))
      | ~ v1_funct_1(F_721)
      | ~ m1_subset_1(E_723,k1_zfmisc_1(k2_zfmisc_1(A_720,B_719)))
      | ~ v1_funct_1(E_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5609,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5565,c_5576])).

tff(c_5628,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_5609])).

tff(c_5783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5570,c_5628])).

tff(c_5784,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5360])).

tff(c_6341,plain,(
    ! [A_773,B_774,C_775,D_776] :
      ( k2_relset_1(A_773,B_774,C_775) = B_774
      | ~ r2_relset_1(B_774,B_774,k1_partfun1(B_774,A_773,A_773,B_774,D_776,C_775),k6_partfun1(B_774))
      | ~ m1_subset_1(D_776,k1_zfmisc_1(k2_zfmisc_1(B_774,A_773)))
      | ~ v1_funct_2(D_776,B_774,A_773)
      | ~ v1_funct_1(D_776)
      | ~ m1_subset_1(C_775,k1_zfmisc_1(k2_zfmisc_1(A_773,B_774)))
      | ~ v1_funct_2(C_775,A_773,B_774)
      | ~ v1_funct_1(C_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6347,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5784,c_6341])).

tff(c_6351,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_5280,c_5296,c_6347])).

tff(c_36,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6360,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6351,c_36])).

tff(c_6366,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5129,c_5218,c_6351,c_6360])).

tff(c_6368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5080,c_6366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.45  
% 6.93/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.45  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.93/2.45  
% 6.93/2.45  %Foreground sorts:
% 6.93/2.45  
% 6.93/2.45  
% 6.93/2.45  %Background operators:
% 6.93/2.45  
% 6.93/2.45  
% 6.93/2.45  %Foreground operators:
% 6.93/2.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.93/2.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.93/2.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.93/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.45  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.93/2.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.93/2.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.93/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.93/2.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.93/2.45  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.93/2.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.93/2.45  tff('#skF_2', type, '#skF_2': $i).
% 6.93/2.45  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.93/2.45  tff('#skF_3', type, '#skF_3': $i).
% 6.93/2.45  tff('#skF_1', type, '#skF_1': $i).
% 6.93/2.45  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.93/2.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.93/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.93/2.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.93/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.93/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.93/2.45  tff('#skF_4', type, '#skF_4': $i).
% 6.93/2.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.93/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.93/2.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.93/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.93/2.45  
% 7.36/2.49  tff(f_122, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.36/2.49  tff(f_49, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.36/2.49  tff(f_181, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.36/2.49  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.36/2.49  tff(f_110, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.36/2.49  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.36/2.49  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.36/2.49  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.36/2.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.36/2.49  tff(f_161, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.36/2.49  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 7.36/2.49  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.36/2.49  tff(f_139, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.36/2.49  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.36/2.49  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.36/2.49  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.36/2.49  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.36/2.49  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 7.36/2.49  tff(c_50, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.36/2.49  tff(c_20, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.36/2.49  tff(c_73, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 7.36/2.49  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.36/2.49  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.36/2.49  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.36/2.49  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.36/2.49  tff(c_4821, plain, (![B_605, D_604, A_606, F_607, E_609, C_608]: (m1_subset_1(k1_partfun1(A_606, B_605, C_608, D_604, E_609, F_607), k1_zfmisc_1(k2_zfmisc_1(A_606, D_604))) | ~m1_subset_1(F_607, k1_zfmisc_1(k2_zfmisc_1(C_608, D_604))) | ~v1_funct_1(F_607) | ~m1_subset_1(E_609, k1_zfmisc_1(k2_zfmisc_1(A_606, B_605))) | ~v1_funct_1(E_609))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.36/2.49  tff(c_46, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.36/2.49  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.36/2.49  tff(c_4522, plain, (![D_570, C_571, A_572, B_573]: (D_570=C_571 | ~r2_relset_1(A_572, B_573, C_571, D_570) | ~m1_subset_1(D_570, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))) | ~m1_subset_1(C_571, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.36/2.49  tff(c_4530, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_4522])).
% 7.36/2.49  tff(c_4545, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4530])).
% 7.36/2.49  tff(c_4628, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4545])).
% 7.36/2.49  tff(c_4834, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4821, c_4628])).
% 7.36/2.49  tff(c_4856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_4834])).
% 7.36/2.49  tff(c_4857, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4545])).
% 7.36/2.49  tff(c_5026, plain, (![F_630, E_628, A_627, C_629, B_632, D_631]: (k1_partfun1(A_627, B_632, C_629, D_631, E_628, F_630)=k5_relat_1(E_628, F_630) | ~m1_subset_1(F_630, k1_zfmisc_1(k2_zfmisc_1(C_629, D_631))) | ~v1_funct_1(F_630) | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(A_627, B_632))) | ~v1_funct_1(E_628))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.36/2.49  tff(c_5030, plain, (![A_627, B_632, E_628]: (k1_partfun1(A_627, B_632, '#skF_2', '#skF_1', E_628, '#skF_4')=k5_relat_1(E_628, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(A_627, B_632))) | ~v1_funct_1(E_628))), inference(resolution, [status(thm)], [c_62, c_5026])).
% 7.36/2.49  tff(c_5059, plain, (![A_637, B_638, E_639]: (k1_partfun1(A_637, B_638, '#skF_2', '#skF_1', E_639, '#skF_4')=k5_relat_1(E_639, '#skF_4') | ~m1_subset_1(E_639, k1_zfmisc_1(k2_zfmisc_1(A_637, B_638))) | ~v1_funct_1(E_639))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5030])).
% 7.36/2.49  tff(c_5068, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5059])).
% 7.36/2.49  tff(c_5075, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4857, c_5068])).
% 7.36/2.49  tff(c_58, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.36/2.49  tff(c_90, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 7.36/2.49  tff(c_125, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.36/2.49  tff(c_138, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_125])).
% 7.36/2.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.36/2.49  tff(c_137, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_125])).
% 7.36/2.49  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.36/2.49  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.36/2.49  tff(c_551, plain, (![A_134, B_133, F_135, C_136, E_137, D_132]: (m1_subset_1(k1_partfun1(A_134, B_133, C_136, D_132, E_137, F_135), k1_zfmisc_1(k2_zfmisc_1(A_134, D_132))) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_136, D_132))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.36/2.49  tff(c_383, plain, (![D_103, C_104, A_105, B_106]: (D_103=C_104 | ~r2_relset_1(A_105, B_106, C_104, D_103) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.36/2.49  tff(c_391, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_383])).
% 7.36/2.49  tff(c_406, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_391])).
% 7.36/2.49  tff(c_432, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_406])).
% 7.36/2.49  tff(c_567, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_551, c_432])).
% 7.36/2.49  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_567])).
% 7.36/2.49  tff(c_591, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_406])).
% 7.36/2.49  tff(c_1041, plain, (![E_177, A_176, D_178, B_175, C_179]: (k1_xboole_0=C_179 | v2_funct_1(D_178) | ~v2_funct_1(k1_partfun1(A_176, B_175, B_175, C_179, D_178, E_177)) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(B_175, C_179))) | ~v1_funct_2(E_177, B_175, C_179) | ~v1_funct_1(E_177) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_175))) | ~v1_funct_2(D_178, A_176, B_175) | ~v1_funct_1(D_178))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.36/2.49  tff(c_1045, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_591, c_1041])).
% 7.36/2.49  tff(c_1049, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_73, c_1045])).
% 7.36/2.49  tff(c_1050, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_90, c_1049])).
% 7.36/2.49  tff(c_14, plain, (![A_6]: (k1_relat_1(A_6)=k1_xboole_0 | k2_relat_1(A_6)!=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.36/2.49  tff(c_145, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_14])).
% 7.36/2.49  tff(c_155, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_145])).
% 7.36/2.49  tff(c_1065, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_155])).
% 7.36/2.49  tff(c_284, plain, (![A_88, B_89, D_90]: (r2_relset_1(A_88, B_89, D_90, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.36/2.49  tff(c_291, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_46, c_284])).
% 7.36/2.49  tff(c_294, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.36/2.49  tff(c_305, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_294])).
% 7.36/2.49  tff(c_1139, plain, (![A_183, B_184, C_185, D_186]: (k2_relset_1(A_183, B_184, C_185)=B_184 | ~r2_relset_1(B_184, B_184, k1_partfun1(B_184, A_183, A_183, B_184, D_186, C_185), k6_partfun1(B_184)) | ~m1_subset_1(D_186, k1_zfmisc_1(k2_zfmisc_1(B_184, A_183))) | ~v1_funct_2(D_186, B_184, A_183) | ~v1_funct_1(D_186) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_2(C_185, A_183, B_184) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.36/2.49  tff(c_1145, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_591, c_1139])).
% 7.36/2.49  tff(c_1149, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_291, c_305, c_1145])).
% 7.36/2.49  tff(c_1151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1065, c_1149])).
% 7.36/2.49  tff(c_1153, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_145])).
% 7.36/2.49  tff(c_1273, plain, (![C_201, B_202, A_203]: (v5_relat_1(C_201, B_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.36/2.49  tff(c_1284, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_1273])).
% 7.36/2.49  tff(c_2575, plain, (![B_345, A_346]: (k2_relat_1(B_345)=A_346 | ~v2_funct_2(B_345, A_346) | ~v5_relat_1(B_345, A_346) | ~v1_relat_1(B_345))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.36/2.49  tff(c_2587, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1284, c_2575])).
% 7.36/2.49  tff(c_2599, plain, (k1_xboole_0='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1153, c_2587])).
% 7.36/2.49  tff(c_2600, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_2599])).
% 7.36/2.49  tff(c_3476, plain, (![A_454, F_457, C_456, D_458, E_455, B_459]: (k1_partfun1(A_454, B_459, C_456, D_458, E_455, F_457)=k5_relat_1(E_455, F_457) | ~m1_subset_1(F_457, k1_zfmisc_1(k2_zfmisc_1(C_456, D_458))) | ~v1_funct_1(F_457) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(A_454, B_459))) | ~v1_funct_1(E_455))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.36/2.49  tff(c_3480, plain, (![A_454, B_459, E_455]: (k1_partfun1(A_454, B_459, '#skF_2', '#skF_1', E_455, '#skF_4')=k5_relat_1(E_455, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(A_454, B_459))) | ~v1_funct_1(E_455))), inference(resolution, [status(thm)], [c_62, c_3476])).
% 7.36/2.49  tff(c_3509, plain, (![A_465, B_466, E_467]: (k1_partfun1(A_465, B_466, '#skF_2', '#skF_1', E_467, '#skF_4')=k5_relat_1(E_467, '#skF_4') | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(A_465, B_466))) | ~v1_funct_1(E_467))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3480])).
% 7.36/2.49  tff(c_3518, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3509])).
% 7.36/2.49  tff(c_3525, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3518])).
% 7.36/2.49  tff(c_2779, plain, (![D_367, C_368, A_369, B_370]: (D_367=C_368 | ~r2_relset_1(A_369, B_370, C_368, D_367) | ~m1_subset_1(D_367, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.36/2.49  tff(c_2787, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_2779])).
% 7.36/2.49  tff(c_2802, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2787])).
% 7.36/2.49  tff(c_3444, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2802])).
% 7.36/2.49  tff(c_3532, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3525, c_3444])).
% 7.36/2.49  tff(c_3538, plain, (![A_470, F_471, C_472, B_469, D_468, E_473]: (m1_subset_1(k1_partfun1(A_470, B_469, C_472, D_468, E_473, F_471), k1_zfmisc_1(k2_zfmisc_1(A_470, D_468))) | ~m1_subset_1(F_471, k1_zfmisc_1(k2_zfmisc_1(C_472, D_468))) | ~v1_funct_1(F_471) | ~m1_subset_1(E_473, k1_zfmisc_1(k2_zfmisc_1(A_470, B_469))) | ~v1_funct_1(E_473))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.36/2.49  tff(c_3568, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3525, c_3538])).
% 7.36/2.49  tff(c_3583, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_3568])).
% 7.36/2.49  tff(c_3612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3532, c_3583])).
% 7.36/2.49  tff(c_3613, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2802])).
% 7.36/2.49  tff(c_4003, plain, (![C_517, D_516, E_515, B_513, A_514]: (k1_xboole_0=C_517 | v2_funct_1(D_516) | ~v2_funct_1(k1_partfun1(A_514, B_513, B_513, C_517, D_516, E_515)) | ~m1_subset_1(E_515, k1_zfmisc_1(k2_zfmisc_1(B_513, C_517))) | ~v1_funct_2(E_515, B_513, C_517) | ~v1_funct_1(E_515) | ~m1_subset_1(D_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_513))) | ~v1_funct_2(D_516, A_514, B_513) | ~v1_funct_1(D_516))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.36/2.49  tff(c_4007, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3613, c_4003])).
% 7.36/2.49  tff(c_4011, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_73, c_4007])).
% 7.36/2.49  tff(c_4012, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_90, c_4011])).
% 7.36/2.49  tff(c_1650, plain, (![B_256, F_258, A_257, C_259, D_255, E_260]: (m1_subset_1(k1_partfun1(A_257, B_256, C_259, D_255, E_260, F_258), k1_zfmisc_1(k2_zfmisc_1(A_257, D_255))) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(C_259, D_255))) | ~v1_funct_1(F_258) | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(A_257, B_256))) | ~v1_funct_1(E_260))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.36/2.49  tff(c_1485, plain, (![D_227, C_228, A_229, B_230]: (D_227=C_228 | ~r2_relset_1(A_229, B_230, C_228, D_227) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.36/2.49  tff(c_1493, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_1485])).
% 7.36/2.49  tff(c_1508, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1493])).
% 7.36/2.49  tff(c_1562, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1508])).
% 7.36/2.49  tff(c_1666, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1650, c_1562])).
% 7.36/2.49  tff(c_1692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_1666])).
% 7.36/2.49  tff(c_1693, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1508])).
% 7.36/2.49  tff(c_2535, plain, (![E_342, A_341, D_343, C_344, B_340]: (k1_xboole_0=C_344 | v2_funct_1(D_343) | ~v2_funct_1(k1_partfun1(A_341, B_340, B_340, C_344, D_343, E_342)) | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(B_340, C_344))) | ~v1_funct_2(E_342, B_340, C_344) | ~v1_funct_1(E_342) | ~m1_subset_1(D_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_340))) | ~v1_funct_2(D_343, A_341, B_340) | ~v1_funct_1(D_343))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.36/2.49  tff(c_2539, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1693, c_2535])).
% 7.36/2.49  tff(c_2543, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_73, c_2539])).
% 7.36/2.49  tff(c_2544, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_90, c_2543])).
% 7.36/2.49  tff(c_1286, plain, (![B_204]: (v2_funct_2(B_204, k2_relat_1(B_204)) | ~v5_relat_1(B_204, k2_relat_1(B_204)) | ~v1_relat_1(B_204))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.36/2.49  tff(c_1292, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_1286])).
% 7.36/2.49  tff(c_1296, plain, (v2_funct_2('#skF_4', k1_xboole_0) | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1153, c_1292])).
% 7.36/2.49  tff(c_1298, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1296])).
% 7.36/2.49  tff(c_2555, plain, (~v5_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2544, c_1298])).
% 7.36/2.49  tff(c_2572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1284, c_2555])).
% 7.36/2.49  tff(c_2573, plain, (v2_funct_2('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1296])).
% 7.36/2.49  tff(c_4024, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4012, c_2573])).
% 7.36/2.49  tff(c_4041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2600, c_4024])).
% 7.36/2.49  tff(c_4042, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2599])).
% 7.36/2.49  tff(c_16, plain, (![A_6]: (k2_relat_1(A_6)=k1_xboole_0 | k1_relat_1(A_6)!=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.36/2.49  tff(c_154, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_16])).
% 7.36/2.49  tff(c_1162, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_154])).
% 7.36/2.49  tff(c_4052, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4042, c_1162])).
% 7.36/2.49  tff(c_1224, plain, (![C_196, A_197, B_198]: (v4_relat_1(C_196, A_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.36/2.49  tff(c_1237, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_1224])).
% 7.36/2.49  tff(c_1180, plain, (![B_189, A_190]: (r1_tarski(k1_relat_1(B_189), A_190) | ~v4_relat_1(B_189, A_190) | ~v1_relat_1(B_189))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.36/2.49  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.36/2.49  tff(c_97, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.36/2.49  tff(c_106, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_97])).
% 7.36/2.49  tff(c_1190, plain, (![B_189]: (k1_relat_1(B_189)=k1_xboole_0 | ~v4_relat_1(B_189, k1_xboole_0) | ~v1_relat_1(B_189))), inference(resolution, [status(thm)], [c_1180, c_106])).
% 7.36/2.49  tff(c_4221, plain, (![B_536]: (k1_relat_1(B_536)='#skF_1' | ~v4_relat_1(B_536, '#skF_1') | ~v1_relat_1(B_536))), inference(demodulation, [status(thm), theory('equality')], [c_4042, c_4042, c_1190])).
% 7.36/2.49  tff(c_4232, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1237, c_4221])).
% 7.36/2.49  tff(c_4245, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_4232])).
% 7.36/2.49  tff(c_4247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4052, c_4245])).
% 7.36/2.49  tff(c_4248, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_154])).
% 7.36/2.49  tff(c_1152, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_145])).
% 7.36/2.49  tff(c_4874, plain, (![B_611, A_612]: (v2_funct_1(B_611) | ~r1_tarski(k2_relat_1(B_611), k1_relat_1(A_612)) | ~v2_funct_1(k5_relat_1(B_611, A_612)) | ~v1_funct_1(B_611) | ~v1_relat_1(B_611) | ~v1_funct_1(A_612) | ~v1_relat_1(A_612))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.36/2.49  tff(c_4892, plain, (![B_611]: (v2_funct_1(B_611) | ~r1_tarski(k2_relat_1(B_611), k1_xboole_0) | ~v2_funct_1(k5_relat_1(B_611, '#skF_4')) | ~v1_funct_1(B_611) | ~v1_relat_1(B_611) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1152, c_4874])).
% 7.36/2.49  tff(c_5004, plain, (![B_626]: (v2_funct_1(B_626) | ~r1_tarski(k2_relat_1(B_626), k1_xboole_0) | ~v2_funct_1(k5_relat_1(B_626, '#skF_4')) | ~v1_funct_1(B_626) | ~v1_relat_1(B_626))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_66, c_4892])).
% 7.36/2.49  tff(c_5013, plain, (v2_funct_1('#skF_3') | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4248, c_5004])).
% 7.36/2.49  tff(c_5022, plain, (v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_72, c_6, c_5013])).
% 7.36/2.49  tff(c_5023, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_90, c_5022])).
% 7.36/2.49  tff(c_5076, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5075, c_5023])).
% 7.36/2.49  tff(c_5079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_5076])).
% 7.36/2.49  tff(c_5080, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 7.36/2.49  tff(c_5116, plain, (![C_646, A_647, B_648]: (v1_relat_1(C_646) | ~m1_subset_1(C_646, k1_zfmisc_1(k2_zfmisc_1(A_647, B_648))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.36/2.49  tff(c_5129, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_5116])).
% 7.36/2.49  tff(c_5206, plain, (![C_661, B_662, A_663]: (v5_relat_1(C_661, B_662) | ~m1_subset_1(C_661, k1_zfmisc_1(k2_zfmisc_1(A_663, B_662))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.36/2.49  tff(c_5218, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_5206])).
% 7.36/2.49  tff(c_5273, plain, (![A_669, B_670, D_671]: (r2_relset_1(A_669, B_670, D_671, D_671) | ~m1_subset_1(D_671, k1_zfmisc_1(k2_zfmisc_1(A_669, B_670))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.36/2.49  tff(c_5280, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_46, c_5273])).
% 7.36/2.49  tff(c_5284, plain, (![A_673, B_674, C_675]: (k2_relset_1(A_673, B_674, C_675)=k2_relat_1(C_675) | ~m1_subset_1(C_675, k1_zfmisc_1(k2_zfmisc_1(A_673, B_674))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.36/2.49  tff(c_5296, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_5284])).
% 7.36/2.49  tff(c_5510, plain, (![F_708, A_705, E_706, C_707, B_710, D_709]: (k1_partfun1(A_705, B_710, C_707, D_709, E_706, F_708)=k5_relat_1(E_706, F_708) | ~m1_subset_1(F_708, k1_zfmisc_1(k2_zfmisc_1(C_707, D_709))) | ~v1_funct_1(F_708) | ~m1_subset_1(E_706, k1_zfmisc_1(k2_zfmisc_1(A_705, B_710))) | ~v1_funct_1(E_706))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.36/2.49  tff(c_5516, plain, (![A_705, B_710, E_706]: (k1_partfun1(A_705, B_710, '#skF_2', '#skF_1', E_706, '#skF_4')=k5_relat_1(E_706, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_706, k1_zfmisc_1(k2_zfmisc_1(A_705, B_710))) | ~v1_funct_1(E_706))), inference(resolution, [status(thm)], [c_62, c_5510])).
% 7.36/2.49  tff(c_5552, plain, (![A_715, B_716, E_717]: (k1_partfun1(A_715, B_716, '#skF_2', '#skF_1', E_717, '#skF_4')=k5_relat_1(E_717, '#skF_4') | ~m1_subset_1(E_717, k1_zfmisc_1(k2_zfmisc_1(A_715, B_716))) | ~v1_funct_1(E_717))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5516])).
% 7.36/2.49  tff(c_5558, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5552])).
% 7.36/2.49  tff(c_5565, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5558])).
% 7.36/2.49  tff(c_5337, plain, (![D_680, C_681, A_682, B_683]: (D_680=C_681 | ~r2_relset_1(A_682, B_683, C_681, D_680) | ~m1_subset_1(D_680, k1_zfmisc_1(k2_zfmisc_1(A_682, B_683))) | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1(A_682, B_683))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.36/2.49  tff(c_5345, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_5337])).
% 7.36/2.49  tff(c_5360, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5345])).
% 7.36/2.49  tff(c_5399, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5360])).
% 7.36/2.49  tff(c_5570, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5565, c_5399])).
% 7.36/2.49  tff(c_5576, plain, (![B_719, E_723, C_722, D_718, F_721, A_720]: (m1_subset_1(k1_partfun1(A_720, B_719, C_722, D_718, E_723, F_721), k1_zfmisc_1(k2_zfmisc_1(A_720, D_718))) | ~m1_subset_1(F_721, k1_zfmisc_1(k2_zfmisc_1(C_722, D_718))) | ~v1_funct_1(F_721) | ~m1_subset_1(E_723, k1_zfmisc_1(k2_zfmisc_1(A_720, B_719))) | ~v1_funct_1(E_723))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.36/2.49  tff(c_5609, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5565, c_5576])).
% 7.36/2.49  tff(c_5628, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_5609])).
% 7.36/2.49  tff(c_5783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5570, c_5628])).
% 7.36/2.49  tff(c_5784, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5360])).
% 7.36/2.49  tff(c_6341, plain, (![A_773, B_774, C_775, D_776]: (k2_relset_1(A_773, B_774, C_775)=B_774 | ~r2_relset_1(B_774, B_774, k1_partfun1(B_774, A_773, A_773, B_774, D_776, C_775), k6_partfun1(B_774)) | ~m1_subset_1(D_776, k1_zfmisc_1(k2_zfmisc_1(B_774, A_773))) | ~v1_funct_2(D_776, B_774, A_773) | ~v1_funct_1(D_776) | ~m1_subset_1(C_775, k1_zfmisc_1(k2_zfmisc_1(A_773, B_774))) | ~v1_funct_2(C_775, A_773, B_774) | ~v1_funct_1(C_775))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.36/2.49  tff(c_6347, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5784, c_6341])).
% 7.36/2.49  tff(c_6351, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_5280, c_5296, c_6347])).
% 7.36/2.49  tff(c_36, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.36/2.49  tff(c_6360, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6351, c_36])).
% 7.36/2.49  tff(c_6366, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5129, c_5218, c_6351, c_6360])).
% 7.36/2.49  tff(c_6368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5080, c_6366])).
% 7.36/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/2.49  
% 7.36/2.49  Inference rules
% 7.36/2.49  ----------------------
% 7.36/2.49  #Ref     : 0
% 7.36/2.49  #Sup     : 1287
% 7.36/2.49  #Fact    : 0
% 7.36/2.49  #Define  : 0
% 7.36/2.49  #Split   : 44
% 7.36/2.49  #Chain   : 0
% 7.36/2.49  #Close   : 0
% 7.36/2.49  
% 7.36/2.49  Ordering : KBO
% 7.36/2.49  
% 7.36/2.49  Simplification rules
% 7.36/2.49  ----------------------
% 7.36/2.49  #Subsume      : 36
% 7.36/2.49  #Demod        : 1458
% 7.36/2.49  #Tautology    : 380
% 7.36/2.49  #SimpNegUnit  : 22
% 7.36/2.49  #BackRed      : 172
% 7.36/2.49  
% 7.36/2.49  #Partial instantiations: 0
% 7.36/2.49  #Strategies tried      : 1
% 7.36/2.49  
% 7.36/2.49  Timing (in seconds)
% 7.36/2.49  ----------------------
% 7.36/2.49  Preprocessing        : 0.35
% 7.36/2.49  Parsing              : 0.18
% 7.36/2.49  CNF conversion       : 0.03
% 7.36/2.49  Main loop            : 1.28
% 7.36/2.49  Inferencing          : 0.45
% 7.36/2.49  Reduction            : 0.47
% 7.36/2.49  Demodulation         : 0.34
% 7.36/2.49  BG Simplification    : 0.05
% 7.36/2.49  Subsumption          : 0.20
% 7.36/2.49  Abstraction          : 0.06
% 7.36/2.49  MUC search           : 0.00
% 7.36/2.49  Cooper               : 0.00
% 7.36/2.49  Total                : 1.69
% 7.36/2.49  Index Insertion      : 0.00
% 7.36/2.49  Index Deletion       : 0.00
% 7.36/2.49  Index Matching       : 0.00
% 7.36/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
