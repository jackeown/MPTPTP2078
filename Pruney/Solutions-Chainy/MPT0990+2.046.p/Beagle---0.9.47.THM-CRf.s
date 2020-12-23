%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:02 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 772 expanded)
%              Number of leaves         :   40 ( 292 expanded)
%              Depth                    :   17
%              Number of atoms          :  326 (3372 expanded)
%              Number of equality atoms :  123 (1260 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_186,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_127,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
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

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_144,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_46,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_160,axiom,(
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

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_93,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_93])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_93])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_119,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_131,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_119])).

tff(c_203,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_212,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_203])).

tff(c_221,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_131,c_212])).

tff(c_222,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_221])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_132,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_141,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_132])).

tff(c_145,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_141])).

tff(c_42,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_10,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_616,plain,(
    ! [A_133,B_134] :
      ( k2_funct_1(A_133) = B_134
      | k6_partfun1(k2_relat_1(A_133)) != k5_relat_1(B_134,A_133)
      | k2_relat_1(B_134) != k1_relat_1(A_133)
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_618,plain,(
    ! [B_134] :
      ( k2_funct_1('#skF_3') = B_134
      | k5_relat_1(B_134,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_134) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_616])).

tff(c_621,plain,(
    ! [B_135] :
      ( k2_funct_1('#skF_3') = B_135
      | k5_relat_1(B_135,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_135) != '#skF_1'
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_72,c_56,c_222,c_618])).

tff(c_627,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_621])).

tff(c_636,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_627])).

tff(c_637,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_636])).

tff(c_639,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_637])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_22,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_73,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_107,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_relset_1(A_54,B_55,D_56,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_114,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_73,c_107])).

tff(c_143,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_132])).

tff(c_372,plain,(
    ! [C_110,A_108,F_109,D_105,E_107,B_106] :
      ( k1_partfun1(A_108,B_106,C_110,D_105,E_107,F_109) = k5_relat_1(E_107,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_110,D_105)))
      | ~ v1_funct_1(F_109)
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_106)))
      | ~ v1_funct_1(E_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_376,plain,(
    ! [A_108,B_106,E_107] :
      ( k1_partfun1(A_108,B_106,'#skF_2','#skF_1',E_107,'#skF_4') = k5_relat_1(E_107,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_106)))
      | ~ v1_funct_1(E_107) ) ),
    inference(resolution,[status(thm)],[c_62,c_372])).

tff(c_388,plain,(
    ! [A_113,B_114,E_115] :
      ( k1_partfun1(A_113,B_114,'#skF_2','#skF_1',E_115,'#skF_4') = k5_relat_1(E_115,'#skF_4')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_376])).

tff(c_397,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_388])).

tff(c_404,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_397])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_273,plain,(
    ! [D_85,C_86,A_87,B_88] :
      ( D_85 = C_86
      | ~ r2_relset_1(A_87,B_88,C_86,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_281,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_273])).

tff(c_296,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_281])).

tff(c_297,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_411,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_297])).

tff(c_520,plain,(
    ! [D_127,E_132,F_130,A_128,B_131,C_129] :
      ( m1_subset_1(k1_partfun1(A_128,B_131,C_129,D_127,E_132,F_130),k1_zfmisc_1(k2_zfmisc_1(A_128,D_127)))
      | ~ m1_subset_1(F_130,k1_zfmisc_1(k2_zfmisc_1(C_129,D_127)))
      | ~ v1_funct_1(F_130)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_128,B_131)))
      | ~ v1_funct_1(E_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_578,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_520])).

tff(c_604,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_578])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_604])).

tff(c_607,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_1315,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_relset_1(A_182,B_183,C_184) = B_183
      | ~ r2_relset_1(B_183,B_183,k1_partfun1(B_183,A_182,A_182,B_183,D_185,C_184),k6_partfun1(B_183))
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(B_183,A_182)))
      | ~ v1_funct_2(D_185,B_183,A_182)
      | ~ v1_funct_1(D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_2(C_184,A_182,B_183)
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1321,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_1315])).

tff(c_1325,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_114,c_143,c_1321])).

tff(c_1327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_639,c_1325])).

tff(c_1328,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_637])).

tff(c_1329,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_637])).

tff(c_1330,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_143])).

tff(c_130,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_119])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_203])).

tff(c_217,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_130,c_209])).

tff(c_218,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_217])).

tff(c_74,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_partfun1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_1333,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_74])).

tff(c_1337,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_66,c_218,c_1333])).

tff(c_1345,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1337])).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_1360,plain,(
    ! [B_194,D_193,C_198,E_195,A_196,F_197] :
      ( k1_partfun1(A_196,B_194,C_198,D_193,E_195,F_197) = k5_relat_1(E_195,F_197)
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(C_198,D_193)))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1364,plain,(
    ! [A_196,B_194,E_195] :
      ( k1_partfun1(A_196,B_194,'#skF_2','#skF_1',E_195,'#skF_4') = k5_relat_1(E_195,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(resolution,[status(thm)],[c_62,c_1360])).

tff(c_1524,plain,(
    ! [A_217,B_218,E_219] :
      ( k1_partfun1(A_217,B_218,'#skF_2','#skF_1',E_219,'#skF_4') = k5_relat_1(E_219,'#skF_4')
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_1(E_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1364])).

tff(c_1533,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1524])).

tff(c_1540,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_607,c_1533])).

tff(c_6,plain,(
    ! [A_2,B_4] :
      ( v2_funct_1(A_2)
      | k2_relat_1(B_4) != k1_relat_1(A_2)
      | ~ v2_funct_1(k5_relat_1(B_4,A_2))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1547,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_6])).

tff(c_1553,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_66,c_106,c_72,c_75,c_145,c_218,c_1547])).

tff(c_1555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1345,c_1553])).

tff(c_1557,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1337])).

tff(c_1558,plain,(
    ! [B_220] :
      ( k2_funct_1('#skF_4') = B_220
      | k5_relat_1(B_220,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_220) != '#skF_2'
      | ~ v1_funct_1(B_220)
      | ~ v1_relat_1(B_220) ) ),
    inference(splitRight,[status(thm)],[c_1337])).

tff(c_1561,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_1558])).

tff(c_1570,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_145,c_1561])).

tff(c_1575,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1570])).

tff(c_1631,plain,(
    ! [F_239,B_236,E_237,D_235,A_238,C_240] :
      ( k1_partfun1(A_238,B_236,C_240,D_235,E_237,F_239) = k5_relat_1(E_237,F_239)
      | ~ m1_subset_1(F_239,k1_zfmisc_1(k2_zfmisc_1(C_240,D_235)))
      | ~ v1_funct_1(F_239)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1635,plain,(
    ! [A_238,B_236,E_237] :
      ( k1_partfun1(A_238,B_236,'#skF_2','#skF_1',E_237,'#skF_4') = k5_relat_1(E_237,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(resolution,[status(thm)],[c_62,c_1631])).

tff(c_1651,plain,(
    ! [A_242,B_243,E_244] :
      ( k1_partfun1(A_242,B_243,'#skF_2','#skF_1',E_244,'#skF_4') = k5_relat_1(E_244,'#skF_4')
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ v1_funct_1(E_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1635])).

tff(c_1660,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1651])).

tff(c_1667,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_607,c_1660])).

tff(c_1669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1575,c_1667])).

tff(c_1670,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1570])).

tff(c_1889,plain,(
    ! [A_278,C_279,B_280] :
      ( k6_partfun1(A_278) = k5_relat_1(C_279,k2_funct_1(C_279))
      | k1_xboole_0 = B_280
      | ~ v2_funct_1(C_279)
      | k2_relset_1(A_278,B_280,C_279) != B_280
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_278,B_280)))
      | ~ v1_funct_2(C_279,A_278,B_280)
      | ~ v1_funct_1(C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1893,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1889])).

tff(c_1901,plain,
    ( k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1330,c_1557,c_1670,c_1893])).

tff(c_1903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1328,c_1901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:30:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.83  
% 4.45/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.83  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.45/1.83  
% 4.45/1.83  %Foreground sorts:
% 4.45/1.83  
% 4.45/1.83  
% 4.45/1.83  %Background operators:
% 4.45/1.83  
% 4.45/1.83  
% 4.45/1.83  %Foreground operators:
% 4.45/1.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.45/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.45/1.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.45/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.45/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.45/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.45/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.45/1.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.45/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.45/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.45/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.45/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.45/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.45/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.45/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.83  
% 4.45/1.86  tff(f_186, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.45/1.86  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.45/1.86  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.45/1.86  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.45/1.86  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.45/1.86  tff(f_127, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.45/1.86  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.45/1.86  tff(f_85, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.45/1.86  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.45/1.86  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.45/1.86  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.45/1.86  tff(f_144, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.45/1.86  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.45/1.86  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.45/1.86  tff(f_160, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 4.45/1.86  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_93, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.45/1.86  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_93])).
% 4.45/1.86  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_93])).
% 4.45/1.86  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_119, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.45/1.86  tff(c_131, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_119])).
% 4.45/1.86  tff(c_203, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.45/1.86  tff(c_212, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_203])).
% 4.45/1.86  tff(c_221, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_131, c_212])).
% 4.45/1.86  tff(c_222, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_221])).
% 4.45/1.86  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_132, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.45/1.86  tff(c_141, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_132])).
% 4.45/1.86  tff(c_145, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_141])).
% 4.45/1.86  tff(c_42, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.45/1.86  tff(c_10, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.45/1.86  tff(c_616, plain, (![A_133, B_134]: (k2_funct_1(A_133)=B_134 | k6_partfun1(k2_relat_1(A_133))!=k5_relat_1(B_134, A_133) | k2_relat_1(B_134)!=k1_relat_1(A_133) | ~v2_funct_1(A_133) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 4.45/1.86  tff(c_618, plain, (![B_134]: (k2_funct_1('#skF_3')=B_134 | k5_relat_1(B_134, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_134)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_134) | ~v1_relat_1(B_134) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_616])).
% 4.45/1.86  tff(c_621, plain, (![B_135]: (k2_funct_1('#skF_3')=B_135 | k5_relat_1(B_135, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_135)!='#skF_1' | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_72, c_56, c_222, c_618])).
% 4.45/1.86  tff(c_627, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_105, c_621])).
% 4.45/1.86  tff(c_636, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_627])).
% 4.45/1.86  tff(c_637, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_636])).
% 4.45/1.86  tff(c_639, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_637])).
% 4.45/1.86  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_22, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.45/1.86  tff(c_73, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 4.45/1.86  tff(c_107, plain, (![A_54, B_55, D_56]: (r2_relset_1(A_54, B_55, D_56, D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.45/1.86  tff(c_114, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_73, c_107])).
% 4.45/1.86  tff(c_143, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_132])).
% 4.45/1.86  tff(c_372, plain, (![C_110, A_108, F_109, D_105, E_107, B_106]: (k1_partfun1(A_108, B_106, C_110, D_105, E_107, F_109)=k5_relat_1(E_107, F_109) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(C_110, D_105))) | ~v1_funct_1(F_109) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_106))) | ~v1_funct_1(E_107))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.45/1.86  tff(c_376, plain, (![A_108, B_106, E_107]: (k1_partfun1(A_108, B_106, '#skF_2', '#skF_1', E_107, '#skF_4')=k5_relat_1(E_107, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_106))) | ~v1_funct_1(E_107))), inference(resolution, [status(thm)], [c_62, c_372])).
% 4.45/1.86  tff(c_388, plain, (![A_113, B_114, E_115]: (k1_partfun1(A_113, B_114, '#skF_2', '#skF_1', E_115, '#skF_4')=k5_relat_1(E_115, '#skF_4') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(E_115))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_376])).
% 4.45/1.86  tff(c_397, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_388])).
% 4.45/1.86  tff(c_404, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_397])).
% 4.45/1.86  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.45/1.86  tff(c_273, plain, (![D_85, C_86, A_87, B_88]: (D_85=C_86 | ~r2_relset_1(A_87, B_88, C_86, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.45/1.86  tff(c_281, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_273])).
% 4.45/1.86  tff(c_296, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_281])).
% 4.45/1.86  tff(c_297, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_296])).
% 4.45/1.86  tff(c_411, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_297])).
% 4.45/1.86  tff(c_520, plain, (![D_127, E_132, F_130, A_128, B_131, C_129]: (m1_subset_1(k1_partfun1(A_128, B_131, C_129, D_127, E_132, F_130), k1_zfmisc_1(k2_zfmisc_1(A_128, D_127))) | ~m1_subset_1(F_130, k1_zfmisc_1(k2_zfmisc_1(C_129, D_127))) | ~v1_funct_1(F_130) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_128, B_131))) | ~v1_funct_1(E_132))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.45/1.86  tff(c_578, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_404, c_520])).
% 4.45/1.86  tff(c_604, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_578])).
% 4.45/1.86  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_411, c_604])).
% 4.45/1.86  tff(c_607, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_296])).
% 4.45/1.86  tff(c_1315, plain, (![A_182, B_183, C_184, D_185]: (k2_relset_1(A_182, B_183, C_184)=B_183 | ~r2_relset_1(B_183, B_183, k1_partfun1(B_183, A_182, A_182, B_183, D_185, C_184), k6_partfun1(B_183)) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(B_183, A_182))) | ~v1_funct_2(D_185, B_183, A_182) | ~v1_funct_1(D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_2(C_184, A_182, B_183) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.45/1.86  tff(c_1321, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_607, c_1315])).
% 4.45/1.86  tff(c_1325, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_114, c_143, c_1321])).
% 4.45/1.86  tff(c_1327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_639, c_1325])).
% 4.45/1.86  tff(c_1328, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_637])).
% 4.45/1.86  tff(c_1329, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_637])).
% 4.45/1.86  tff(c_1330, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_143])).
% 4.45/1.86  tff(c_130, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_119])).
% 4.45/1.86  tff(c_209, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_203])).
% 4.45/1.86  tff(c_217, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_130, c_209])).
% 4.45/1.86  tff(c_218, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_217])).
% 4.45/1.86  tff(c_74, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_partfun1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 4.45/1.86  tff(c_1333, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1329, c_74])).
% 4.45/1.86  tff(c_1337, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_66, c_218, c_1333])).
% 4.45/1.86  tff(c_1345, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1337])).
% 4.45/1.86  tff(c_4, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.45/1.86  tff(c_75, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4])).
% 4.45/1.86  tff(c_1360, plain, (![B_194, D_193, C_198, E_195, A_196, F_197]: (k1_partfun1(A_196, B_194, C_198, D_193, E_195, F_197)=k5_relat_1(E_195, F_197) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(C_198, D_193))) | ~v1_funct_1(F_197) | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_194))) | ~v1_funct_1(E_195))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.45/1.86  tff(c_1364, plain, (![A_196, B_194, E_195]: (k1_partfun1(A_196, B_194, '#skF_2', '#skF_1', E_195, '#skF_4')=k5_relat_1(E_195, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_194))) | ~v1_funct_1(E_195))), inference(resolution, [status(thm)], [c_62, c_1360])).
% 4.45/1.86  tff(c_1524, plain, (![A_217, B_218, E_219]: (k1_partfun1(A_217, B_218, '#skF_2', '#skF_1', E_219, '#skF_4')=k5_relat_1(E_219, '#skF_4') | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_1(E_219))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1364])).
% 4.45/1.86  tff(c_1533, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1524])).
% 4.45/1.86  tff(c_1540, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_607, c_1533])).
% 4.45/1.86  tff(c_6, plain, (![A_2, B_4]: (v2_funct_1(A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(k5_relat_1(B_4, A_2)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.45/1.86  tff(c_1547, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1540, c_6])).
% 4.45/1.86  tff(c_1553, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_66, c_106, c_72, c_75, c_145, c_218, c_1547])).
% 4.45/1.86  tff(c_1555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1345, c_1553])).
% 4.45/1.86  tff(c_1557, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1337])).
% 4.45/1.86  tff(c_1558, plain, (![B_220]: (k2_funct_1('#skF_4')=B_220 | k5_relat_1(B_220, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_220)!='#skF_2' | ~v1_funct_1(B_220) | ~v1_relat_1(B_220))), inference(splitRight, [status(thm)], [c_1337])).
% 4.45/1.86  tff(c_1561, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_1558])).
% 4.45/1.86  tff(c_1570, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_145, c_1561])).
% 4.45/1.86  tff(c_1575, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1570])).
% 4.45/1.86  tff(c_1631, plain, (![F_239, B_236, E_237, D_235, A_238, C_240]: (k1_partfun1(A_238, B_236, C_240, D_235, E_237, F_239)=k5_relat_1(E_237, F_239) | ~m1_subset_1(F_239, k1_zfmisc_1(k2_zfmisc_1(C_240, D_235))) | ~v1_funct_1(F_239) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_236))) | ~v1_funct_1(E_237))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.45/1.86  tff(c_1635, plain, (![A_238, B_236, E_237]: (k1_partfun1(A_238, B_236, '#skF_2', '#skF_1', E_237, '#skF_4')=k5_relat_1(E_237, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_236))) | ~v1_funct_1(E_237))), inference(resolution, [status(thm)], [c_62, c_1631])).
% 4.45/1.86  tff(c_1651, plain, (![A_242, B_243, E_244]: (k1_partfun1(A_242, B_243, '#skF_2', '#skF_1', E_244, '#skF_4')=k5_relat_1(E_244, '#skF_4') | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~v1_funct_1(E_244))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1635])).
% 4.45/1.86  tff(c_1660, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1651])).
% 4.45/1.86  tff(c_1667, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_607, c_1660])).
% 4.45/1.86  tff(c_1669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1575, c_1667])).
% 4.45/1.86  tff(c_1670, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1570])).
% 4.45/1.86  tff(c_1889, plain, (![A_278, C_279, B_280]: (k6_partfun1(A_278)=k5_relat_1(C_279, k2_funct_1(C_279)) | k1_xboole_0=B_280 | ~v2_funct_1(C_279) | k2_relset_1(A_278, B_280, C_279)!=B_280 | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_278, B_280))) | ~v1_funct_2(C_279, A_278, B_280) | ~v1_funct_1(C_279))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.45/1.86  tff(c_1893, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1889])).
% 4.45/1.86  tff(c_1901, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1330, c_1557, c_1670, c_1893])).
% 4.45/1.86  tff(c_1903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1328, c_1901])).
% 4.45/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.86  
% 4.45/1.86  Inference rules
% 4.45/1.86  ----------------------
% 4.45/1.86  #Ref     : 0
% 4.45/1.86  #Sup     : 390
% 4.45/1.86  #Fact    : 0
% 4.45/1.86  #Define  : 0
% 4.45/1.86  #Split   : 20
% 4.45/1.86  #Chain   : 0
% 4.45/1.86  #Close   : 0
% 4.45/1.86  
% 4.45/1.86  Ordering : KBO
% 4.45/1.86  
% 4.45/1.86  Simplification rules
% 4.45/1.86  ----------------------
% 4.45/1.86  #Subsume      : 20
% 4.45/1.86  #Demod        : 439
% 4.45/1.86  #Tautology    : 107
% 4.45/1.86  #SimpNegUnit  : 42
% 4.45/1.86  #BackRed      : 19
% 4.45/1.86  
% 4.45/1.86  #Partial instantiations: 0
% 4.45/1.86  #Strategies tried      : 1
% 4.45/1.86  
% 4.45/1.86  Timing (in seconds)
% 4.45/1.86  ----------------------
% 4.45/1.86  Preprocessing        : 0.37
% 4.45/1.86  Parsing              : 0.20
% 4.45/1.86  CNF conversion       : 0.03
% 4.45/1.86  Main loop            : 0.66
% 4.45/1.86  Inferencing          : 0.24
% 4.45/1.86  Reduction            : 0.23
% 4.45/1.86  Demodulation         : 0.16
% 4.45/1.86  BG Simplification    : 0.03
% 4.45/1.86  Subsumption          : 0.11
% 4.45/1.86  Abstraction          : 0.03
% 4.45/1.86  MUC search           : 0.00
% 4.45/1.86  Cooper               : 0.00
% 4.45/1.86  Total                : 1.08
% 4.45/1.86  Index Insertion      : 0.00
% 4.45/1.86  Index Deletion       : 0.00
% 4.45/1.86  Index Matching       : 0.00
% 4.45/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
