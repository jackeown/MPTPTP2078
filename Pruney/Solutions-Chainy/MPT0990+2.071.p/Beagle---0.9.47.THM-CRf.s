%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:06 EST 2020

% Result     : Theorem 8.28s
% Output     : CNFRefutation 8.68s
% Verified   : 
% Statistics : Number of formulae       :  233 (2654 expanded)
%              Number of leaves         :   49 ( 946 expanded)
%              Depth                    :   22
%              Number of atoms          :  595 (11127 expanded)
%              Number of equality atoms :  194 (3933 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_242,negated_conjecture,(
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

tff(f_155,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_145,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_141,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_157,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
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

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_32,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_216,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_174,axiom,(
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

tff(f_200,axiom,(
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

tff(c_96,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_90,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_420,plain,(
    ! [B_104,C_108,D_103,A_106,E_105,F_107] :
      ( k1_partfun1(A_106,B_104,C_108,D_103,E_105,F_107) = k5_relat_1(E_105,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_108,D_103)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_424,plain,(
    ! [A_106,B_104,E_105] :
      ( k1_partfun1(A_106,B_104,'#skF_3','#skF_2',E_105,'#skF_5') = k5_relat_1(E_105,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(resolution,[status(thm)],[c_86,c_420])).

tff(c_435,plain,(
    ! [A_110,B_111,E_112] :
      ( k1_partfun1(A_110,B_111,'#skF_3','#skF_2',E_112,'#skF_5') = k5_relat_1(E_112,'#skF_5')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(E_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_424])).

tff(c_444,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_435])).

tff(c_451,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_444])).

tff(c_54,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_82,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_308,plain,(
    ! [D_83,C_84,A_85,B_86] :
      ( D_83 = C_84
      | ~ r2_relset_1(A_85,B_86,C_84,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_316,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_82,c_308])).

tff(c_331,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_316])).

tff(c_332,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_458,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_332])).

tff(c_580,plain,(
    ! [D_138,C_133,A_137,E_135,B_134,F_136] :
      ( m1_subset_1(k1_partfun1(A_137,B_134,C_133,D_138,E_135,F_136),k1_zfmisc_1(k2_zfmisc_1(A_137,D_138)))
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_133,D_138)))
      | ~ v1_funct_1(F_136)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_619,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_580])).

tff(c_640,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_619])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_640])).

tff(c_643,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_692,plain,(
    ! [B_144,C_143,F_146,D_148,E_145,A_147] :
      ( v1_funct_1(k1_partfun1(A_147,B_144,C_143,D_148,E_145,F_146))
      | ~ m1_subset_1(F_146,k1_zfmisc_1(k2_zfmisc_1(C_143,D_148)))
      | ~ v1_funct_1(F_146)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_696,plain,(
    ! [A_147,B_144,E_145] :
      ( v1_funct_1(k1_partfun1(A_147,B_144,'#skF_3','#skF_2',E_145,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(resolution,[status(thm)],[c_86,c_692])).

tff(c_706,plain,(
    ! [A_149,B_150,E_151] :
      ( v1_funct_1(k1_partfun1(A_149,B_150,'#skF_3','#skF_2',E_151,'#skF_5'))
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_696])).

tff(c_715,plain,
    ( v1_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_706])).

tff(c_722,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_643,c_715])).

tff(c_58,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_12,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [A_4] : k2_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_18,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,(
    ! [A_6] : v1_relat_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18])).

tff(c_176,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_189,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_176])).

tff(c_80,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_84,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_252,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_261,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_252])).

tff(c_266,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_261])).

tff(c_36,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_652,plain,(
    ! [A_139,B_140] :
      ( k2_funct_1(A_139) = B_140
      | k6_partfun1(k2_relat_1(A_139)) != k5_relat_1(B_140,A_139)
      | k2_relat_1(B_140) != k1_relat_1(A_139)
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36])).

tff(c_656,plain,(
    ! [B_140] :
      ( k2_funct_1('#skF_4') = B_140
      | k5_relat_1(B_140,'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(B_140) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_652])).

tff(c_665,plain,(
    ! [B_141] :
      ( k2_funct_1('#skF_4') = B_141
      | k5_relat_1(B_141,'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(B_141) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_80,c_656])).

tff(c_677,plain,(
    ! [A_6] :
      ( k6_partfun1(A_6) = k2_funct_1('#skF_4')
      | k5_relat_1(k6_partfun1(A_6),'#skF_4') != k6_partfun1('#skF_3')
      | k2_relat_1(k6_partfun1(A_6)) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(k6_partfun1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_99,c_665])).

tff(c_687,plain,(
    ! [A_6] :
      ( k6_partfun1(A_6) = k2_funct_1('#skF_4')
      | k5_relat_1(k6_partfun1(A_6),'#skF_4') != k6_partfun1('#skF_3')
      | k1_relat_1('#skF_4') != A_6
      | ~ v1_funct_1(k6_partfun1(A_6)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_677])).

tff(c_726,plain,
    ( k6_partfun1('#skF_2') = k2_funct_1('#skF_4')
    | k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') != k6_partfun1('#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_722,c_687])).

tff(c_746,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_726])).

tff(c_14,plain,(
    ! [A_5] :
      ( v1_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_funct_1(A_5))
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_112,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_120,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_76])).

tff(c_94,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_72,plain,(
    ! [A_49,C_51,B_50] :
      ( k6_partfun1(A_49) = k5_relat_1(C_51,k2_funct_1(C_51))
      | k1_xboole_0 = B_50
      | ~ v2_funct_1(C_51)
      | k2_relset_1(A_49,B_50,C_51) != B_50
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(C_51,A_49,B_50)
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_2084,plain,(
    ! [A_255,C_256,B_257] :
      ( k6_partfun1(A_255) = k5_relat_1(C_256,k2_funct_1(C_256))
      | B_257 = '#skF_1'
      | ~ v2_funct_1(C_256)
      | k2_relset_1(A_255,B_257,C_256) != B_257
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_257)))
      | ~ v1_funct_2(C_256,A_255,B_257)
      | ~ v1_funct_1(C_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_72])).

tff(c_2090,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_2084])).

tff(c_2100,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_2090])).

tff(c_2101,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_2100])).

tff(c_38,plain,(
    ! [A_13] :
      ( k2_funct_1(k2_funct_1(A_13)) = A_13
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_296,plain,(
    ! [A_82] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_82),A_82)) = k2_relat_1(A_82)
      | ~ v2_funct_1(A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2971,plain,(
    ! [A_297] :
      ( k2_relat_1(k5_relat_1(A_297,k2_funct_1(A_297))) = k2_relat_1(k2_funct_1(A_297))
      | ~ v2_funct_1(k2_funct_1(A_297))
      | ~ v1_funct_1(k2_funct_1(A_297))
      | ~ v1_relat_1(k2_funct_1(A_297))
      | ~ v2_funct_1(A_297)
      | ~ v1_funct_1(A_297)
      | ~ v1_relat_1(A_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_296])).

tff(c_2982,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2101,c_2971])).

tff(c_2992,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_80,c_100,c_2982])).

tff(c_2995,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2992])).

tff(c_2998,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_2995])).

tff(c_3002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_2998])).

tff(c_3003,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2992])).

tff(c_3018,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3003])).

tff(c_3021,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_3018])).

tff(c_3025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_80,c_3021])).

tff(c_3026,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3003])).

tff(c_3028,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3026])).

tff(c_3035,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_3028])).

tff(c_3039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_3035])).

tff(c_3040,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3026])).

tff(c_28,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3047,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3040,c_28])).

tff(c_3056,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_80,c_3047])).

tff(c_3058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_3056])).

tff(c_3060,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_726])).

tff(c_74,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_188,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_176])).

tff(c_671,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_188,c_665])).

tff(c_683,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_671])).

tff(c_684,plain,
    ( k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3')
    | k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_683])).

tff(c_688,plain,(
    k2_relat_1('#skF_5') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_3063,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3060,c_688])).

tff(c_88,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_217,plain,(
    ! [A_71,B_72,D_73] :
      ( r2_relset_1(A_71,B_72,D_73,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_224,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_54,c_217])).

tff(c_264,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_252])).

tff(c_3888,plain,(
    ! [A_363,B_364,C_365,D_366] :
      ( k2_relset_1(A_363,B_364,C_365) = B_364
      | ~ r2_relset_1(B_364,B_364,k1_partfun1(B_364,A_363,A_363,B_364,D_366,C_365),k6_partfun1(B_364))
      | ~ m1_subset_1(D_366,k1_zfmisc_1(k2_zfmisc_1(B_364,A_363)))
      | ~ v1_funct_2(D_366,B_364,A_363)
      | ~ v1_funct_1(D_366)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364)))
      | ~ v1_funct_2(C_365,A_363,B_364)
      | ~ v1_funct_1(C_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_3897,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_3888])).

tff(c_3904,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_96,c_94,c_92,c_224,c_264,c_3897])).

tff(c_3906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3063,c_3904])).

tff(c_3907,plain,(
    k5_relat_1('#skF_5','#skF_4') != k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_5441,plain,(
    ! [C_513,A_511,D_508,E_510,F_512,B_509] :
      ( k1_partfun1(A_511,B_509,C_513,D_508,E_510,F_512) = k5_relat_1(E_510,F_512)
      | ~ m1_subset_1(F_512,k1_zfmisc_1(k2_zfmisc_1(C_513,D_508)))
      | ~ v1_funct_1(F_512)
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(A_511,B_509)))
      | ~ v1_funct_1(E_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5445,plain,(
    ! [A_511,B_509,E_510] :
      ( k1_partfun1(A_511,B_509,'#skF_3','#skF_2',E_510,'#skF_5') = k5_relat_1(E_510,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_510,k1_zfmisc_1(k2_zfmisc_1(A_511,B_509)))
      | ~ v1_funct_1(E_510) ) ),
    inference(resolution,[status(thm)],[c_86,c_5441])).

tff(c_6122,plain,(
    ! [A_557,B_558,E_559] :
      ( k1_partfun1(A_557,B_558,'#skF_3','#skF_2',E_559,'#skF_5') = k5_relat_1(E_559,'#skF_5')
      | ~ m1_subset_1(E_559,k1_zfmisc_1(k2_zfmisc_1(A_557,B_558)))
      | ~ v1_funct_1(E_559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5445])).

tff(c_6140,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_6122])).

tff(c_6154,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_643,c_6140])).

tff(c_5410,plain,(
    ! [F_502,B_500,C_499,D_504,A_503,E_501] :
      ( v1_funct_1(k1_partfun1(A_503,B_500,C_499,D_504,E_501,F_502))
      | ~ m1_subset_1(F_502,k1_zfmisc_1(k2_zfmisc_1(C_499,D_504)))
      | ~ v1_funct_1(F_502)
      | ~ m1_subset_1(E_501,k1_zfmisc_1(k2_zfmisc_1(A_503,B_500)))
      | ~ v1_funct_1(E_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_5414,plain,(
    ! [A_503,B_500,E_501] :
      ( v1_funct_1(k1_partfun1(A_503,B_500,'#skF_3','#skF_2',E_501,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_501,k1_zfmisc_1(k2_zfmisc_1(A_503,B_500)))
      | ~ v1_funct_1(E_501) ) ),
    inference(resolution,[status(thm)],[c_86,c_5410])).

tff(c_5424,plain,(
    ! [A_505,B_506,E_507] :
      ( v1_funct_1(k1_partfun1(A_505,B_506,'#skF_3','#skF_2',E_507,'#skF_5'))
      | ~ m1_subset_1(E_507,k1_zfmisc_1(k2_zfmisc_1(A_505,B_506)))
      | ~ v1_funct_1(E_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_5414])).

tff(c_5433,plain,
    ( v1_funct_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_5424])).

tff(c_5440,plain,(
    v1_funct_1(k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_643,c_5433])).

tff(c_5458,plain,
    ( k6_partfun1('#skF_2') = k2_funct_1('#skF_4')
    | k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') != k6_partfun1('#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_5440,c_687])).

tff(c_5478,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5458])).

tff(c_10,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [A_4] : k1_relat_1(k6_partfun1(A_4)) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10])).

tff(c_5581,plain,(
    ! [A_529,C_530,B_531] :
      ( k6_partfun1(A_529) = k5_relat_1(C_530,k2_funct_1(C_530))
      | B_531 = '#skF_1'
      | ~ v2_funct_1(C_530)
      | k2_relset_1(A_529,B_531,C_530) != B_531
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_529,B_531)))
      | ~ v1_funct_2(C_530,A_529,B_531)
      | ~ v1_funct_1(C_530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_72])).

tff(c_5587,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_5581])).

tff(c_5597,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_5587])).

tff(c_5598,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_5597])).

tff(c_271,plain,(
    ! [A_80] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_80),A_80)) = k2_relat_1(A_80)
      | ~ v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_280,plain,(
    ! [A_13] :
      ( k1_relat_1(k5_relat_1(A_13,k2_funct_1(A_13))) = k2_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_271])).

tff(c_5605,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1(k6_partfun1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5598,c_280])).

tff(c_5611,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_80,c_101,c_5605])).

tff(c_5623,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5611])).

tff(c_5626,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_5623])).

tff(c_5630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_5626])).

tff(c_5631,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5611])).

tff(c_5640,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5631])).

tff(c_5708,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_5640])).

tff(c_5712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_80,c_5708])).

tff(c_5713,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5631])).

tff(c_5715,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5713])).

tff(c_5722,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_5715])).

tff(c_5726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_5722])).

tff(c_5727,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5713])).

tff(c_5734,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5727,c_28])).

tff(c_5743,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_96,c_80,c_5734])).

tff(c_5745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5478,c_5743])).

tff(c_5747,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5458])).

tff(c_3908,plain,(
    k2_relat_1('#skF_5') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_97,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_partfun1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36])).

tff(c_3912,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_5') = B_12
      | k6_partfun1(k1_relat_1('#skF_4')) != k5_relat_1(B_12,'#skF_5')
      | k2_relat_1(B_12) != k1_relat_1('#skF_5')
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3908,c_97])).

tff(c_3916,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_5') = B_12
      | k6_partfun1(k1_relat_1('#skF_4')) != k5_relat_1(B_12,'#skF_5')
      | k2_relat_1(B_12) != k1_relat_1('#skF_5')
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_90,c_3912])).

tff(c_3924,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3916])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_121,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_78])).

tff(c_20,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_98,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_20])).

tff(c_64,plain,(
    ! [E_48,D_46,C_45,A_43,B_44] :
      ( k1_xboole_0 = C_45
      | v2_funct_1(E_48)
      | k2_relset_1(A_43,B_44,D_46) != B_44
      | ~ v2_funct_1(k1_partfun1(A_43,B_44,B_44,C_45,D_46,E_48))
      | ~ m1_subset_1(E_48,k1_zfmisc_1(k2_zfmisc_1(B_44,C_45)))
      | ~ v1_funct_2(E_48,B_44,C_45)
      | ~ v1_funct_1(E_48)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_2(D_46,A_43,B_44)
      | ~ v1_funct_1(D_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_5351,plain,(
    ! [B_491,C_488,E_487,D_489,A_490] :
      ( C_488 = '#skF_1'
      | v2_funct_1(E_487)
      | k2_relset_1(A_490,B_491,D_489) != B_491
      | ~ v2_funct_1(k1_partfun1(A_490,B_491,B_491,C_488,D_489,E_487))
      | ~ m1_subset_1(E_487,k1_zfmisc_1(k2_zfmisc_1(B_491,C_488)))
      | ~ v1_funct_2(E_487,B_491,C_488)
      | ~ v1_funct_1(E_487)
      | ~ m1_subset_1(D_489,k1_zfmisc_1(k2_zfmisc_1(A_490,B_491)))
      | ~ v1_funct_2(D_489,A_490,B_491)
      | ~ v1_funct_1(D_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_64])).

tff(c_5357,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_5351])).

tff(c_5365,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_90,c_88,c_86,c_98,c_84,c_5357])).

tff(c_5367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3924,c_121,c_5365])).

tff(c_5368,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_5') = B_12
      | k6_partfun1(k1_relat_1('#skF_4')) != k5_relat_1(B_12,'#skF_5')
      | k2_relat_1(B_12) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(splitRight,[status(thm)],[c_3916])).

tff(c_5860,plain,(
    ! [B_544] :
      ( k2_funct_1('#skF_5') = B_544
      | k5_relat_1(B_544,'#skF_5') != k6_partfun1('#skF_2')
      | k2_relat_1(B_544) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_544)
      | ~ v1_relat_1(B_544) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5747,c_5368])).

tff(c_5863,plain,
    ( k2_funct_1('#skF_5') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_5') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_5860])).

tff(c_5875,plain,
    ( k2_funct_1('#skF_5') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_5') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_266,c_5863])).

tff(c_6287,plain,
    ( k2_funct_1('#skF_5') = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6154,c_5875])).

tff(c_6288,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6287])).

tff(c_5369,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3916])).

tff(c_3909,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3908,c_264])).

tff(c_5752,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5747,c_3909])).

tff(c_5883,plain,(
    ! [A_545,C_546,B_547] :
      ( k6_partfun1(A_545) = k5_relat_1(C_546,k2_funct_1(C_546))
      | B_547 = '#skF_1'
      | ~ v2_funct_1(C_546)
      | k2_relset_1(A_545,B_547,C_546) != B_547
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(A_545,B_547)))
      | ~ v1_funct_2(C_546,A_545,B_547)
      | ~ v1_funct_1(C_546) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_72])).

tff(c_5887,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_5883])).

tff(c_5895,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_5752,c_5369,c_5887])).

tff(c_5896,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_5895])).

tff(c_305,plain,(
    ! [A_13] :
      ( k2_relat_1(k5_relat_1(A_13,k2_funct_1(A_13))) = k2_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(k2_funct_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_296])).

tff(c_5918,plain,
    ( k2_relat_1(k6_partfun1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5896,c_305])).

tff(c_5925,plain,
    ( k2_relat_1(k2_funct_1('#skF_5')) = '#skF_3'
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_90,c_5369,c_100,c_5918])).

tff(c_6377,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5925])).

tff(c_6380,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_6377])).

tff(c_6384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_90,c_6380])).

tff(c_6385,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1(k2_funct_1('#skF_5'))
    | k2_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5925])).

tff(c_6409,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6385])).

tff(c_6412,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_6409])).

tff(c_6416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_90,c_5369,c_6412])).

tff(c_6417,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_5'))
    | k2_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6385])).

tff(c_6420,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6417])).

tff(c_6423,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_6420])).

tff(c_6427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_90,c_6423])).

tff(c_6428,plain,(
    k2_relat_1(k2_funct_1('#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6417])).

tff(c_6435,plain,
    ( k1_relat_1('#skF_5') = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6428,c_28])).

tff(c_6444,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_90,c_5369,c_6435])).

tff(c_6446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6288,c_6444])).

tff(c_6447,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6287])).

tff(c_6449,plain,(
    k5_relat_1('#skF_5','#skF_4') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6447,c_5896])).

tff(c_6453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3907,c_6449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.28/2.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.28/2.98  
% 8.28/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.28/2.98  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.28/2.98  
% 8.28/2.98  %Foreground sorts:
% 8.28/2.98  
% 8.28/2.98  
% 8.28/2.98  %Background operators:
% 8.28/2.98  
% 8.28/2.98  
% 8.28/2.98  %Foreground operators:
% 8.28/2.98  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.28/2.98  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 8.28/2.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.28/2.98  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.28/2.98  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.28/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.28/2.98  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.28/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.28/2.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.28/2.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.28/2.98  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.28/2.98  tff('#skF_5', type, '#skF_5': $i).
% 8.28/2.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.28/2.98  tff('#skF_2', type, '#skF_2': $i).
% 8.28/2.98  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.28/2.98  tff('#skF_3', type, '#skF_3': $i).
% 8.28/2.98  tff('#skF_1', type, '#skF_1': $i).
% 8.28/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.28/2.98  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.28/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.28/2.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.28/2.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.28/2.98  tff('#skF_4', type, '#skF_4': $i).
% 8.28/2.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.28/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.28/2.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.28/2.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.28/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.28/2.98  
% 8.68/3.01  tff(f_242, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 8.68/3.01  tff(f_155, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.68/3.01  tff(f_145, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.68/3.01  tff(f_129, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.68/3.01  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.68/3.01  tff(f_157, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.68/3.01  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.68/3.01  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.68/3.01  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.68/3.01  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.68/3.01  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 8.68/3.01  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.68/3.01  tff(f_68, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 8.68/3.01  tff(f_32, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 8.68/3.01  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.68/3.01  tff(f_216, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 8.68/3.01  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 8.68/3.01  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 8.68/3.01  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.68/3.01  tff(f_174, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 8.68/3.01  tff(f_200, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 8.68/3.01  tff(c_96, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_92, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_90, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_420, plain, (![B_104, C_108, D_103, A_106, E_105, F_107]: (k1_partfun1(A_106, B_104, C_108, D_103, E_105, F_107)=k5_relat_1(E_105, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_108, D_103))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_104))) | ~v1_funct_1(E_105))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.68/3.01  tff(c_424, plain, (![A_106, B_104, E_105]: (k1_partfun1(A_106, B_104, '#skF_3', '#skF_2', E_105, '#skF_5')=k5_relat_1(E_105, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_104))) | ~v1_funct_1(E_105))), inference(resolution, [status(thm)], [c_86, c_420])).
% 8.68/3.01  tff(c_435, plain, (![A_110, B_111, E_112]: (k1_partfun1(A_110, B_111, '#skF_3', '#skF_2', E_112, '#skF_5')=k5_relat_1(E_112, '#skF_5') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(E_112))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_424])).
% 8.68/3.01  tff(c_444, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_435])).
% 8.68/3.01  tff(c_451, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_444])).
% 8.68/3.01  tff(c_54, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.68/3.01  tff(c_82, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_308, plain, (![D_83, C_84, A_85, B_86]: (D_83=C_84 | ~r2_relset_1(A_85, B_86, C_84, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.68/3.01  tff(c_316, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_82, c_308])).
% 8.68/3.01  tff(c_331, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_316])).
% 8.68/3.01  tff(c_332, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_331])).
% 8.68/3.01  tff(c_458, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_451, c_332])).
% 8.68/3.01  tff(c_580, plain, (![D_138, C_133, A_137, E_135, B_134, F_136]: (m1_subset_1(k1_partfun1(A_137, B_134, C_133, D_138, E_135, F_136), k1_zfmisc_1(k2_zfmisc_1(A_137, D_138))) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_133, D_138))) | ~v1_funct_1(F_136) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_134))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.68/3.01  tff(c_619, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_451, c_580])).
% 8.68/3.01  tff(c_640, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_619])).
% 8.68/3.01  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_458, c_640])).
% 8.68/3.01  tff(c_643, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_331])).
% 8.68/3.01  tff(c_692, plain, (![B_144, C_143, F_146, D_148, E_145, A_147]: (v1_funct_1(k1_partfun1(A_147, B_144, C_143, D_148, E_145, F_146)) | ~m1_subset_1(F_146, k1_zfmisc_1(k2_zfmisc_1(C_143, D_148))) | ~v1_funct_1(F_146) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_144))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.68/3.01  tff(c_696, plain, (![A_147, B_144, E_145]: (v1_funct_1(k1_partfun1(A_147, B_144, '#skF_3', '#skF_2', E_145, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_144))) | ~v1_funct_1(E_145))), inference(resolution, [status(thm)], [c_86, c_692])).
% 8.68/3.01  tff(c_706, plain, (![A_149, B_150, E_151]: (v1_funct_1(k1_partfun1(A_149, B_150, '#skF_3', '#skF_2', E_151, '#skF_5')) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(E_151))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_696])).
% 8.68/3.01  tff(c_715, plain, (v1_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_706])).
% 8.68/3.01  tff(c_722, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_643, c_715])).
% 8.68/3.01  tff(c_58, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.68/3.01  tff(c_12, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.68/3.01  tff(c_100, plain, (![A_4]: (k2_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12])).
% 8.68/3.01  tff(c_18, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.68/3.01  tff(c_99, plain, (![A_6]: (v1_relat_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18])).
% 8.68/3.01  tff(c_176, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.68/3.01  tff(c_189, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_176])).
% 8.68/3.01  tff(c_80, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_84, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_252, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.68/3.01  tff(c_261, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_252])).
% 8.68/3.01  tff(c_266, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_261])).
% 8.68/3.01  tff(c_36, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.68/3.01  tff(c_652, plain, (![A_139, B_140]: (k2_funct_1(A_139)=B_140 | k6_partfun1(k2_relat_1(A_139))!=k5_relat_1(B_140, A_139) | k2_relat_1(B_140)!=k1_relat_1(A_139) | ~v2_funct_1(A_139) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36])).
% 8.68/3.01  tff(c_656, plain, (![B_140]: (k2_funct_1('#skF_4')=B_140 | k5_relat_1(B_140, '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(B_140)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_140) | ~v1_relat_1(B_140) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_652])).
% 8.68/3.01  tff(c_665, plain, (![B_141]: (k2_funct_1('#skF_4')=B_141 | k5_relat_1(B_141, '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(B_141)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_141) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_80, c_656])).
% 8.68/3.01  tff(c_677, plain, (![A_6]: (k6_partfun1(A_6)=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1(A_6), '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1(k6_partfun1(A_6))!=k1_relat_1('#skF_4') | ~v1_funct_1(k6_partfun1(A_6)))), inference(resolution, [status(thm)], [c_99, c_665])).
% 8.68/3.01  tff(c_687, plain, (![A_6]: (k6_partfun1(A_6)=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1(A_6), '#skF_4')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!=A_6 | ~v1_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_677])).
% 8.68/3.01  tff(c_726, plain, (k6_partfun1('#skF_2')=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_722, c_687])).
% 8.68/3.01  tff(c_746, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_726])).
% 8.68/3.01  tff(c_14, plain, (![A_5]: (v1_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.68/3.01  tff(c_22, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.68/3.01  tff(c_16, plain, (![A_5]: (v1_relat_1(k2_funct_1(A_5)) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.68/3.01  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.68/3.01  tff(c_104, plain, (![A_55]: (k1_xboole_0=A_55 | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.68/3.01  tff(c_112, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_104])).
% 8.68/3.01  tff(c_76, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_120, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_76])).
% 8.68/3.01  tff(c_94, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_72, plain, (![A_49, C_51, B_50]: (k6_partfun1(A_49)=k5_relat_1(C_51, k2_funct_1(C_51)) | k1_xboole_0=B_50 | ~v2_funct_1(C_51) | k2_relset_1(A_49, B_50, C_51)!=B_50 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(C_51, A_49, B_50) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.68/3.01  tff(c_2084, plain, (![A_255, C_256, B_257]: (k6_partfun1(A_255)=k5_relat_1(C_256, k2_funct_1(C_256)) | B_257='#skF_1' | ~v2_funct_1(C_256) | k2_relset_1(A_255, B_257, C_256)!=B_257 | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_257))) | ~v1_funct_2(C_256, A_255, B_257) | ~v1_funct_1(C_256))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_72])).
% 8.68/3.01  tff(c_2090, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_2084])).
% 8.68/3.01  tff(c_2100, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_2090])).
% 8.68/3.01  tff(c_2101, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_120, c_2100])).
% 8.68/3.01  tff(c_38, plain, (![A_13]: (k2_funct_1(k2_funct_1(A_13))=A_13 | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.68/3.01  tff(c_296, plain, (![A_82]: (k2_relat_1(k5_relat_1(k2_funct_1(A_82), A_82))=k2_relat_1(A_82) | ~v2_funct_1(A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.68/3.01  tff(c_2971, plain, (![A_297]: (k2_relat_1(k5_relat_1(A_297, k2_funct_1(A_297)))=k2_relat_1(k2_funct_1(A_297)) | ~v2_funct_1(k2_funct_1(A_297)) | ~v1_funct_1(k2_funct_1(A_297)) | ~v1_relat_1(k2_funct_1(A_297)) | ~v2_funct_1(A_297) | ~v1_funct_1(A_297) | ~v1_relat_1(A_297))), inference(superposition, [status(thm), theory('equality')], [c_38, c_296])).
% 8.68/3.01  tff(c_2982, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2101, c_2971])).
% 8.68/3.01  tff(c_2992, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_80, c_100, c_2982])).
% 8.68/3.01  tff(c_2995, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2992])).
% 8.68/3.01  tff(c_2998, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_2995])).
% 8.68/3.01  tff(c_3002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_2998])).
% 8.68/3.01  tff(c_3003, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_2992])).
% 8.68/3.01  tff(c_3018, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3003])).
% 8.68/3.01  tff(c_3021, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_3018])).
% 8.68/3.01  tff(c_3025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_80, c_3021])).
% 8.68/3.01  tff(c_3026, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_3003])).
% 8.68/3.01  tff(c_3028, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3026])).
% 8.68/3.01  tff(c_3035, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_3028])).
% 8.68/3.01  tff(c_3039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_3035])).
% 8.68/3.01  tff(c_3040, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_3026])).
% 8.68/3.01  tff(c_28, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.68/3.01  tff(c_3047, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3040, c_28])).
% 8.68/3.01  tff(c_3056, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_80, c_3047])).
% 8.68/3.01  tff(c_3058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_746, c_3056])).
% 8.68/3.01  tff(c_3060, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_726])).
% 8.68/3.01  tff(c_74, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_188, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_176])).
% 8.68/3.01  tff(c_671, plain, (k2_funct_1('#skF_4')='#skF_5' | k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_188, c_665])).
% 8.68/3.01  tff(c_683, plain, (k2_funct_1('#skF_4')='#skF_5' | k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_671])).
% 8.68/3.01  tff(c_684, plain, (k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3') | k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_683])).
% 8.68/3.01  tff(c_688, plain, (k2_relat_1('#skF_5')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_684])).
% 8.68/3.01  tff(c_3063, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3060, c_688])).
% 8.68/3.01  tff(c_88, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_217, plain, (![A_71, B_72, D_73]: (r2_relset_1(A_71, B_72, D_73, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.68/3.01  tff(c_224, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_54, c_217])).
% 8.68/3.01  tff(c_264, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_252])).
% 8.68/3.01  tff(c_3888, plain, (![A_363, B_364, C_365, D_366]: (k2_relset_1(A_363, B_364, C_365)=B_364 | ~r2_relset_1(B_364, B_364, k1_partfun1(B_364, A_363, A_363, B_364, D_366, C_365), k6_partfun1(B_364)) | ~m1_subset_1(D_366, k1_zfmisc_1(k2_zfmisc_1(B_364, A_363))) | ~v1_funct_2(D_366, B_364, A_363) | ~v1_funct_1(D_366) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))) | ~v1_funct_2(C_365, A_363, B_364) | ~v1_funct_1(C_365))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.68/3.01  tff(c_3897, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_643, c_3888])).
% 8.68/3.01  tff(c_3904, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_96, c_94, c_92, c_224, c_264, c_3897])).
% 8.68/3.01  tff(c_3906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3063, c_3904])).
% 8.68/3.01  tff(c_3907, plain, (k5_relat_1('#skF_5', '#skF_4')!=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_684])).
% 8.68/3.01  tff(c_5441, plain, (![C_513, A_511, D_508, E_510, F_512, B_509]: (k1_partfun1(A_511, B_509, C_513, D_508, E_510, F_512)=k5_relat_1(E_510, F_512) | ~m1_subset_1(F_512, k1_zfmisc_1(k2_zfmisc_1(C_513, D_508))) | ~v1_funct_1(F_512) | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(A_511, B_509))) | ~v1_funct_1(E_510))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.68/3.01  tff(c_5445, plain, (![A_511, B_509, E_510]: (k1_partfun1(A_511, B_509, '#skF_3', '#skF_2', E_510, '#skF_5')=k5_relat_1(E_510, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_510, k1_zfmisc_1(k2_zfmisc_1(A_511, B_509))) | ~v1_funct_1(E_510))), inference(resolution, [status(thm)], [c_86, c_5441])).
% 8.68/3.01  tff(c_6122, plain, (![A_557, B_558, E_559]: (k1_partfun1(A_557, B_558, '#skF_3', '#skF_2', E_559, '#skF_5')=k5_relat_1(E_559, '#skF_5') | ~m1_subset_1(E_559, k1_zfmisc_1(k2_zfmisc_1(A_557, B_558))) | ~v1_funct_1(E_559))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_5445])).
% 8.68/3.01  tff(c_6140, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_6122])).
% 8.68/3.01  tff(c_6154, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_643, c_6140])).
% 8.68/3.01  tff(c_5410, plain, (![F_502, B_500, C_499, D_504, A_503, E_501]: (v1_funct_1(k1_partfun1(A_503, B_500, C_499, D_504, E_501, F_502)) | ~m1_subset_1(F_502, k1_zfmisc_1(k2_zfmisc_1(C_499, D_504))) | ~v1_funct_1(F_502) | ~m1_subset_1(E_501, k1_zfmisc_1(k2_zfmisc_1(A_503, B_500))) | ~v1_funct_1(E_501))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.68/3.01  tff(c_5414, plain, (![A_503, B_500, E_501]: (v1_funct_1(k1_partfun1(A_503, B_500, '#skF_3', '#skF_2', E_501, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_501, k1_zfmisc_1(k2_zfmisc_1(A_503, B_500))) | ~v1_funct_1(E_501))), inference(resolution, [status(thm)], [c_86, c_5410])).
% 8.68/3.01  tff(c_5424, plain, (![A_505, B_506, E_507]: (v1_funct_1(k1_partfun1(A_505, B_506, '#skF_3', '#skF_2', E_507, '#skF_5')) | ~m1_subset_1(E_507, k1_zfmisc_1(k2_zfmisc_1(A_505, B_506))) | ~v1_funct_1(E_507))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_5414])).
% 8.68/3.01  tff(c_5433, plain, (v1_funct_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_5424])).
% 8.68/3.01  tff(c_5440, plain, (v1_funct_1(k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_643, c_5433])).
% 8.68/3.01  tff(c_5458, plain, (k6_partfun1('#skF_2')=k2_funct_1('#skF_4') | k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')!=k6_partfun1('#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(resolution, [status(thm)], [c_5440, c_687])).
% 8.68/3.01  tff(c_5478, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_5458])).
% 8.68/3.01  tff(c_10, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.68/3.01  tff(c_101, plain, (![A_4]: (k1_relat_1(k6_partfun1(A_4))=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10])).
% 8.68/3.01  tff(c_5581, plain, (![A_529, C_530, B_531]: (k6_partfun1(A_529)=k5_relat_1(C_530, k2_funct_1(C_530)) | B_531='#skF_1' | ~v2_funct_1(C_530) | k2_relset_1(A_529, B_531, C_530)!=B_531 | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_529, B_531))) | ~v1_funct_2(C_530, A_529, B_531) | ~v1_funct_1(C_530))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_72])).
% 8.68/3.01  tff(c_5587, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_5581])).
% 8.68/3.01  tff(c_5597, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_5587])).
% 8.68/3.01  tff(c_5598, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_120, c_5597])).
% 8.68/3.01  tff(c_271, plain, (![A_80]: (k1_relat_1(k5_relat_1(k2_funct_1(A_80), A_80))=k2_relat_1(A_80) | ~v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.68/3.01  tff(c_280, plain, (![A_13]: (k1_relat_1(k5_relat_1(A_13, k2_funct_1(A_13)))=k2_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_38, c_271])).
% 8.68/3.01  tff(c_5605, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1(k6_partfun1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5598, c_280])).
% 8.68/3.01  tff(c_5611, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_80, c_101, c_5605])).
% 8.68/3.01  tff(c_5623, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5611])).
% 8.68/3.01  tff(c_5626, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_5623])).
% 8.68/3.01  tff(c_5630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_5626])).
% 8.68/3.01  tff(c_5631, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_5611])).
% 8.68/3.01  tff(c_5640, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5631])).
% 8.68/3.01  tff(c_5708, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_5640])).
% 8.68/3.01  tff(c_5712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_80, c_5708])).
% 8.68/3.01  tff(c_5713, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_5631])).
% 8.68/3.01  tff(c_5715, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5713])).
% 8.68/3.01  tff(c_5722, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_5715])).
% 8.68/3.01  tff(c_5726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_5722])).
% 8.68/3.01  tff(c_5727, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_5713])).
% 8.68/3.01  tff(c_5734, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5727, c_28])).
% 8.68/3.01  tff(c_5743, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_96, c_80, c_5734])).
% 8.68/3.01  tff(c_5745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5478, c_5743])).
% 8.68/3.01  tff(c_5747, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_5458])).
% 8.68/3.01  tff(c_3908, plain, (k2_relat_1('#skF_5')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_684])).
% 8.68/3.01  tff(c_97, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_partfun1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36])).
% 8.68/3.01  tff(c_3912, plain, (![B_12]: (k2_funct_1('#skF_5')=B_12 | k6_partfun1(k1_relat_1('#skF_4'))!=k5_relat_1(B_12, '#skF_5') | k2_relat_1(B_12)!=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3908, c_97])).
% 8.68/3.01  tff(c_3916, plain, (![B_12]: (k2_funct_1('#skF_5')=B_12 | k6_partfun1(k1_relat_1('#skF_4'))!=k5_relat_1(B_12, '#skF_5') | k2_relat_1(B_12)!=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_90, c_3912])).
% 8.68/3.01  tff(c_3924, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_3916])).
% 8.68/3.01  tff(c_78, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_242])).
% 8.68/3.01  tff(c_121, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_78])).
% 8.68/3.01  tff(c_20, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.68/3.01  tff(c_98, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_20])).
% 8.68/3.01  tff(c_64, plain, (![E_48, D_46, C_45, A_43, B_44]: (k1_xboole_0=C_45 | v2_funct_1(E_48) | k2_relset_1(A_43, B_44, D_46)!=B_44 | ~v2_funct_1(k1_partfun1(A_43, B_44, B_44, C_45, D_46, E_48)) | ~m1_subset_1(E_48, k1_zfmisc_1(k2_zfmisc_1(B_44, C_45))) | ~v1_funct_2(E_48, B_44, C_45) | ~v1_funct_1(E_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | ~v1_funct_2(D_46, A_43, B_44) | ~v1_funct_1(D_46))), inference(cnfTransformation, [status(thm)], [f_200])).
% 8.68/3.01  tff(c_5351, plain, (![B_491, C_488, E_487, D_489, A_490]: (C_488='#skF_1' | v2_funct_1(E_487) | k2_relset_1(A_490, B_491, D_489)!=B_491 | ~v2_funct_1(k1_partfun1(A_490, B_491, B_491, C_488, D_489, E_487)) | ~m1_subset_1(E_487, k1_zfmisc_1(k2_zfmisc_1(B_491, C_488))) | ~v1_funct_2(E_487, B_491, C_488) | ~v1_funct_1(E_487) | ~m1_subset_1(D_489, k1_zfmisc_1(k2_zfmisc_1(A_490, B_491))) | ~v1_funct_2(D_489, A_490, B_491) | ~v1_funct_1(D_489))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_64])).
% 8.68/3.01  tff(c_5357, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_643, c_5351])).
% 8.68/3.01  tff(c_5365, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_90, c_88, c_86, c_98, c_84, c_5357])).
% 8.68/3.01  tff(c_5367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3924, c_121, c_5365])).
% 8.68/3.01  tff(c_5368, plain, (![B_12]: (k2_funct_1('#skF_5')=B_12 | k6_partfun1(k1_relat_1('#skF_4'))!=k5_relat_1(B_12, '#skF_5') | k2_relat_1(B_12)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(splitRight, [status(thm)], [c_3916])).
% 8.68/3.01  tff(c_5860, plain, (![B_544]: (k2_funct_1('#skF_5')=B_544 | k5_relat_1(B_544, '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1(B_544)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_544) | ~v1_relat_1(B_544))), inference(demodulation, [status(thm), theory('equality')], [c_5747, c_5368])).
% 8.68/3.01  tff(c_5863, plain, (k2_funct_1('#skF_5')='#skF_4' | k5_relat_1('#skF_4', '#skF_5')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_189, c_5860])).
% 8.68/3.01  tff(c_5875, plain, (k2_funct_1('#skF_5')='#skF_4' | k5_relat_1('#skF_4', '#skF_5')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_266, c_5863])).
% 8.68/3.01  tff(c_6287, plain, (k2_funct_1('#skF_5')='#skF_4' | k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6154, c_5875])).
% 8.68/3.01  tff(c_6288, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_6287])).
% 8.68/3.01  tff(c_5369, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_3916])).
% 8.68/3.01  tff(c_3909, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3908, c_264])).
% 8.68/3.01  tff(c_5752, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5747, c_3909])).
% 8.68/3.01  tff(c_5883, plain, (![A_545, C_546, B_547]: (k6_partfun1(A_545)=k5_relat_1(C_546, k2_funct_1(C_546)) | B_547='#skF_1' | ~v2_funct_1(C_546) | k2_relset_1(A_545, B_547, C_546)!=B_547 | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(A_545, B_547))) | ~v1_funct_2(C_546, A_545, B_547) | ~v1_funct_1(C_546))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_72])).
% 8.68/3.01  tff(c_5887, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_86, c_5883])).
% 8.68/3.01  tff(c_5895, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_5752, c_5369, c_5887])).
% 8.68/3.01  tff(c_5896, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_121, c_5895])).
% 8.68/3.01  tff(c_305, plain, (![A_13]: (k2_relat_1(k5_relat_1(A_13, k2_funct_1(A_13)))=k2_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(k2_funct_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_38, c_296])).
% 8.68/3.01  tff(c_5918, plain, (k2_relat_1(k6_partfun1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5896, c_305])).
% 8.68/3.01  tff(c_5925, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_3' | ~v2_funct_1(k2_funct_1('#skF_5')) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_90, c_5369, c_100, c_5918])).
% 8.68/3.01  tff(c_6377, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_5925])).
% 8.68/3.01  tff(c_6380, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_6377])).
% 8.68/3.01  tff(c_6384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_90, c_6380])).
% 8.68/3.01  tff(c_6385, plain, (~v1_funct_1(k2_funct_1('#skF_5')) | ~v2_funct_1(k2_funct_1('#skF_5')) | k2_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_5925])).
% 8.68/3.01  tff(c_6409, plain, (~v2_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_6385])).
% 8.68/3.01  tff(c_6412, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_6409])).
% 8.68/3.01  tff(c_6416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_90, c_5369, c_6412])).
% 8.68/3.01  tff(c_6417, plain, (~v1_funct_1(k2_funct_1('#skF_5')) | k2_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_6385])).
% 8.68/3.01  tff(c_6420, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_6417])).
% 8.68/3.01  tff(c_6423, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_6420])).
% 8.68/3.01  tff(c_6427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_90, c_6423])).
% 8.68/3.01  tff(c_6428, plain, (k2_relat_1(k2_funct_1('#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_6417])).
% 8.68/3.01  tff(c_6435, plain, (k1_relat_1('#skF_5')='#skF_3' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6428, c_28])).
% 8.68/3.01  tff(c_6444, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_90, c_5369, c_6435])).
% 8.68/3.01  tff(c_6446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6288, c_6444])).
% 8.68/3.01  tff(c_6447, plain, (k2_funct_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_6287])).
% 8.68/3.01  tff(c_6449, plain, (k5_relat_1('#skF_5', '#skF_4')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6447, c_5896])).
% 8.68/3.01  tff(c_6453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3907, c_6449])).
% 8.68/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.68/3.01  
% 8.68/3.01  Inference rules
% 8.68/3.01  ----------------------
% 8.68/3.01  #Ref     : 0
% 8.68/3.01  #Sup     : 1330
% 8.68/3.01  #Fact    : 0
% 8.68/3.01  #Define  : 0
% 8.68/3.01  #Split   : 54
% 8.68/3.01  #Chain   : 0
% 8.68/3.01  #Close   : 0
% 8.68/3.01  
% 8.68/3.01  Ordering : KBO
% 8.68/3.01  
% 8.68/3.01  Simplification rules
% 8.68/3.01  ----------------------
% 8.68/3.01  #Subsume      : 60
% 8.68/3.01  #Demod        : 1730
% 8.68/3.01  #Tautology    : 360
% 8.68/3.01  #SimpNegUnit  : 152
% 8.68/3.01  #BackRed      : 56
% 8.68/3.01  
% 8.68/3.01  #Partial instantiations: 0
% 8.68/3.01  #Strategies tried      : 1
% 8.68/3.01  
% 8.68/3.01  Timing (in seconds)
% 8.68/3.02  ----------------------
% 8.68/3.02  Preprocessing        : 0.41
% 8.68/3.02  Parsing              : 0.21
% 8.68/3.02  CNF conversion       : 0.03
% 8.68/3.02  Main loop            : 1.80
% 8.68/3.02  Inferencing          : 0.60
% 8.68/3.02  Reduction            : 0.70
% 8.68/3.02  Demodulation         : 0.52
% 8.68/3.02  BG Simplification    : 0.06
% 8.68/3.02  Subsumption          : 0.32
% 8.68/3.02  Abstraction          : 0.08
% 8.68/3.02  MUC search           : 0.00
% 8.68/3.02  Cooper               : 0.00
% 8.68/3.02  Total                : 2.28
% 8.68/3.02  Index Insertion      : 0.00
% 8.68/3.02  Index Deletion       : 0.00
% 8.68/3.02  Index Matching       : 0.00
% 8.68/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
