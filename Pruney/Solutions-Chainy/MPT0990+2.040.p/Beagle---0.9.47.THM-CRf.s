%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:01 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 758 expanded)
%              Number of leaves         :   41 ( 288 expanded)
%              Depth                    :   17
%              Number of atoms          :  325 (3361 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_127,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
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

tff(f_115,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_44,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_42,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

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

tff(c_91,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_102,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_91])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_103,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_91])).

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

tff(c_117,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_129,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_117])).

tff(c_201,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_210,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_201])).

tff(c_219,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_129,c_210])).

tff(c_220,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_219])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_147,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_156,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_147])).

tff(c_160,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_156])).

tff(c_42,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_634,plain,(
    ! [A_143,B_144] :
      ( k2_funct_1(A_143) = B_144
      | k6_partfun1(k2_relat_1(A_143)) != k5_relat_1(B_144,A_143)
      | k2_relat_1(B_144) != k1_relat_1(A_143)
      | ~ v2_funct_1(A_143)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_636,plain,(
    ! [B_144] :
      ( k2_funct_1('#skF_3') = B_144
      | k5_relat_1(B_144,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_144) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_634])).

tff(c_639,plain,(
    ! [B_145] :
      ( k2_funct_1('#skF_3') = B_145
      | k5_relat_1(B_145,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_145) != '#skF_1'
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_72,c_56,c_220,c_636])).

tff(c_648,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_639])).

tff(c_655,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_648])).

tff(c_656,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_655])).

tff(c_657,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_38,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_105,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_112,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_38,c_105])).

tff(c_158,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_147])).

tff(c_370,plain,(
    ! [E_108,B_107,A_109,C_111,F_110,D_106] :
      ( k1_partfun1(A_109,B_107,C_111,D_106,E_108,F_110) = k5_relat_1(E_108,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_111,D_106)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_374,plain,(
    ! [A_109,B_107,E_108] :
      ( k1_partfun1(A_109,B_107,'#skF_2','#skF_1',E_108,'#skF_4') = k5_relat_1(E_108,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(resolution,[status(thm)],[c_62,c_370])).

tff(c_447,plain,(
    ! [A_121,B_122,E_123] :
      ( k1_partfun1(A_121,B_122,'#skF_2','#skF_1',E_123,'#skF_4') = k5_relat_1(E_123,'#skF_4')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_1(E_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_374])).

tff(c_456,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_447])).

tff(c_463,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_456])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_271,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( D_86 = C_87
      | ~ r2_relset_1(A_88,B_89,C_87,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_279,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_271])).

tff(c_294,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_279])).

tff(c_295,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_470,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_295])).

tff(c_539,plain,(
    ! [C_137,A_141,D_142,B_138,F_140,E_139] :
      ( m1_subset_1(k1_partfun1(A_141,B_138,C_137,D_142,E_139,F_140),k1_zfmisc_1(k2_zfmisc_1(A_141,D_142)))
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_137,D_142)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_138)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_593,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_539])).

tff(c_622,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_593])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_622])).

tff(c_625,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_1216,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( k2_relset_1(A_187,B_188,C_189) = B_188
      | ~ r2_relset_1(B_188,B_188,k1_partfun1(B_188,A_187,A_187,B_188,D_190,C_189),k6_partfun1(B_188))
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(B_188,A_187)))
      | ~ v1_funct_2(D_190,B_188,A_187)
      | ~ v1_funct_1(D_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(C_189,A_187,B_188)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1222,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_1216])).

tff(c_1226,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_112,c_158,c_1222])).

tff(c_1228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_657,c_1226])).

tff(c_1229,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_1230,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_1231,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_158])).

tff(c_128,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_207,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_201])).

tff(c_215,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_128,c_207])).

tff(c_216,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_215])).

tff(c_73,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_partfun1(k2_relat_1(A_5)) != k5_relat_1(B_7,A_5)
      | k2_relat_1(B_7) != k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_1234,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_73])).

tff(c_1238,plain,(
    ! [B_7] :
      ( k2_funct_1('#skF_4') = B_7
      | k5_relat_1(B_7,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_7) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_216,c_1234])).

tff(c_1246,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1238])).

tff(c_6,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_1261,plain,(
    ! [C_203,B_199,F_202,E_200,D_198,A_201] :
      ( k1_partfun1(A_201,B_199,C_203,D_198,E_200,F_202) = k5_relat_1(E_200,F_202)
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(C_203,D_198)))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_199)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1265,plain,(
    ! [A_201,B_199,E_200] :
      ( k1_partfun1(A_201,B_199,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_199)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_62,c_1261])).

tff(c_1425,plain,(
    ! [A_222,B_223,E_224] :
      ( k1_partfun1(A_222,B_223,'#skF_2','#skF_1',E_224,'#skF_4') = k5_relat_1(E_224,'#skF_4')
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_1(E_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1265])).

tff(c_1434,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1425])).

tff(c_1441,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_625,c_1434])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( v2_funct_1(A_1)
      | k2_relat_1(B_3) != k1_relat_1(A_1)
      | ~ v2_funct_1(k5_relat_1(B_3,A_1))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1448,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1441,c_2])).

tff(c_1454,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_66,c_103,c_72,c_74,c_160,c_216,c_1448])).

tff(c_1456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1246,c_1454])).

tff(c_1458,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1238])).

tff(c_1459,plain,(
    ! [B_225] :
      ( k2_funct_1('#skF_4') = B_225
      | k5_relat_1(B_225,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_225) != '#skF_2'
      | ~ v1_funct_1(B_225)
      | ~ v1_relat_1(B_225) ) ),
    inference(splitRight,[status(thm)],[c_1238])).

tff(c_1465,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_1459])).

tff(c_1472,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_160,c_1465])).

tff(c_1476,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1472])).

tff(c_1532,plain,(
    ! [C_245,E_242,A_243,D_240,F_244,B_241] :
      ( k1_partfun1(A_243,B_241,C_245,D_240,E_242,F_244) = k5_relat_1(E_242,F_244)
      | ~ m1_subset_1(F_244,k1_zfmisc_1(k2_zfmisc_1(C_245,D_240)))
      | ~ v1_funct_1(F_244)
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1536,plain,(
    ! [A_243,B_241,E_242] :
      ( k1_partfun1(A_243,B_241,'#skF_2','#skF_1',E_242,'#skF_4') = k5_relat_1(E_242,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(resolution,[status(thm)],[c_62,c_1532])).

tff(c_1552,plain,(
    ! [A_247,B_248,E_249] :
      ( k1_partfun1(A_247,B_248,'#skF_2','#skF_1',E_249,'#skF_4') = k5_relat_1(E_249,'#skF_4')
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248)))
      | ~ v1_funct_1(E_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1536])).

tff(c_1561,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1552])).

tff(c_1568,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_625,c_1561])).

tff(c_1570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1476,c_1568])).

tff(c_1571,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1472])).

tff(c_1790,plain,(
    ! [A_283,C_284,B_285] :
      ( k6_partfun1(A_283) = k5_relat_1(C_284,k2_funct_1(C_284))
      | k1_xboole_0 = B_285
      | ~ v2_funct_1(C_284)
      | k2_relset_1(A_283,B_285,C_284) != B_285
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_283,B_285)))
      | ~ v1_funct_2(C_284,A_283,B_285)
      | ~ v1_funct_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1794,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1790])).

tff(c_1802,plain,
    ( k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1231,c_1458,c_1571,c_1794])).

tff(c_1804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1229,c_1802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.74  
% 4.23/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.23/1.74  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.23/1.74  
% 4.23/1.74  %Foreground sorts:
% 4.23/1.74  
% 4.23/1.74  
% 4.23/1.74  %Background operators:
% 4.23/1.74  
% 4.23/1.74  
% 4.23/1.74  %Foreground operators:
% 4.23/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.23/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.23/1.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.23/1.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.74  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.23/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.23/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.23/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.23/1.74  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.23/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.23/1.74  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.23/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.23/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.23/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.23/1.74  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.23/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.23/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.23/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.23/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.23/1.74  
% 4.55/1.76  tff(f_186, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.55/1.76  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.55/1.76  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.55/1.76  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.55/1.76  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.55/1.76  tff(f_127, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.55/1.76  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.55/1.76  tff(f_115, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.55/1.76  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.55/1.76  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.55/1.76  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.55/1.76  tff(f_144, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.55/1.76  tff(f_44, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.55/1.76  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.55/1.76  tff(f_160, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 4.55/1.76  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_91, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.55/1.76  tff(c_102, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_91])).
% 4.55/1.76  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_103, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_91])).
% 4.55/1.76  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_117, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.55/1.76  tff(c_129, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_117])).
% 4.55/1.76  tff(c_201, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.55/1.76  tff(c_210, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_201])).
% 4.55/1.76  tff(c_219, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_129, c_210])).
% 4.55/1.76  tff(c_220, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_219])).
% 4.55/1.76  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_147, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.55/1.76  tff(c_156, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_147])).
% 4.55/1.76  tff(c_160, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_156])).
% 4.55/1.76  tff(c_42, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.55/1.76  tff(c_8, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.55/1.76  tff(c_634, plain, (![A_143, B_144]: (k2_funct_1(A_143)=B_144 | k6_partfun1(k2_relat_1(A_143))!=k5_relat_1(B_144, A_143) | k2_relat_1(B_144)!=k1_relat_1(A_143) | ~v2_funct_1(A_143) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 4.55/1.76  tff(c_636, plain, (![B_144]: (k2_funct_1('#skF_3')=B_144 | k5_relat_1(B_144, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_144)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_634])).
% 4.55/1.76  tff(c_639, plain, (![B_145]: (k2_funct_1('#skF_3')=B_145 | k5_relat_1(B_145, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_145)!='#skF_1' | ~v1_funct_1(B_145) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_72, c_56, c_220, c_636])).
% 4.55/1.76  tff(c_648, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_639])).
% 4.55/1.76  tff(c_655, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_648])).
% 4.55/1.76  tff(c_656, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_655])).
% 4.55/1.76  tff(c_657, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_656])).
% 4.55/1.76  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_38, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.55/1.76  tff(c_105, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.55/1.76  tff(c_112, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_38, c_105])).
% 4.55/1.76  tff(c_158, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_147])).
% 4.55/1.76  tff(c_370, plain, (![E_108, B_107, A_109, C_111, F_110, D_106]: (k1_partfun1(A_109, B_107, C_111, D_106, E_108, F_110)=k5_relat_1(E_108, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_111, D_106))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_107))) | ~v1_funct_1(E_108))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.55/1.76  tff(c_374, plain, (![A_109, B_107, E_108]: (k1_partfun1(A_109, B_107, '#skF_2', '#skF_1', E_108, '#skF_4')=k5_relat_1(E_108, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_107))) | ~v1_funct_1(E_108))), inference(resolution, [status(thm)], [c_62, c_370])).
% 4.55/1.76  tff(c_447, plain, (![A_121, B_122, E_123]: (k1_partfun1(A_121, B_122, '#skF_2', '#skF_1', E_123, '#skF_4')=k5_relat_1(E_123, '#skF_4') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_1(E_123))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_374])).
% 4.55/1.76  tff(c_456, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_447])).
% 4.55/1.76  tff(c_463, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_456])).
% 4.55/1.76  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.55/1.76  tff(c_271, plain, (![D_86, C_87, A_88, B_89]: (D_86=C_87 | ~r2_relset_1(A_88, B_89, C_87, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.55/1.76  tff(c_279, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_271])).
% 4.55/1.76  tff(c_294, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_279])).
% 4.55/1.76  tff(c_295, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_294])).
% 4.55/1.76  tff(c_470, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_295])).
% 4.55/1.76  tff(c_539, plain, (![C_137, A_141, D_142, B_138, F_140, E_139]: (m1_subset_1(k1_partfun1(A_141, B_138, C_137, D_142, E_139, F_140), k1_zfmisc_1(k2_zfmisc_1(A_141, D_142))) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_137, D_142))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_138))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.55/1.76  tff(c_593, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_463, c_539])).
% 4.55/1.76  tff(c_622, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_593])).
% 4.55/1.76  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_470, c_622])).
% 4.55/1.76  tff(c_625, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_294])).
% 4.55/1.76  tff(c_1216, plain, (![A_187, B_188, C_189, D_190]: (k2_relset_1(A_187, B_188, C_189)=B_188 | ~r2_relset_1(B_188, B_188, k1_partfun1(B_188, A_187, A_187, B_188, D_190, C_189), k6_partfun1(B_188)) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(B_188, A_187))) | ~v1_funct_2(D_190, B_188, A_187) | ~v1_funct_1(D_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(C_189, A_187, B_188) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.55/1.76  tff(c_1222, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_625, c_1216])).
% 4.55/1.76  tff(c_1226, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_112, c_158, c_1222])).
% 4.55/1.76  tff(c_1228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_657, c_1226])).
% 4.55/1.76  tff(c_1229, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_656])).
% 4.55/1.76  tff(c_1230, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_656])).
% 4.55/1.76  tff(c_1231, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_158])).
% 4.55/1.76  tff(c_128, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_117])).
% 4.55/1.76  tff(c_207, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_201])).
% 4.55/1.76  tff(c_215, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_128, c_207])).
% 4.55/1.76  tff(c_216, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_215])).
% 4.55/1.76  tff(c_73, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_partfun1(k2_relat_1(A_5))!=k5_relat_1(B_7, A_5) | k2_relat_1(B_7)!=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 4.55/1.76  tff(c_1234, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_73])).
% 4.55/1.76  tff(c_1238, plain, (![B_7]: (k2_funct_1('#skF_4')=B_7 | k5_relat_1(B_7, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_7)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_216, c_1234])).
% 4.55/1.76  tff(c_1246, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1238])).
% 4.55/1.76  tff(c_6, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.55/1.76  tff(c_74, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 4.55/1.76  tff(c_1261, plain, (![C_203, B_199, F_202, E_200, D_198, A_201]: (k1_partfun1(A_201, B_199, C_203, D_198, E_200, F_202)=k5_relat_1(E_200, F_202) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(C_203, D_198))) | ~v1_funct_1(F_202) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_199))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.55/1.76  tff(c_1265, plain, (![A_201, B_199, E_200]: (k1_partfun1(A_201, B_199, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_199))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_62, c_1261])).
% 4.55/1.76  tff(c_1425, plain, (![A_222, B_223, E_224]: (k1_partfun1(A_222, B_223, '#skF_2', '#skF_1', E_224, '#skF_4')=k5_relat_1(E_224, '#skF_4') | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~v1_funct_1(E_224))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1265])).
% 4.55/1.76  tff(c_1434, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1425])).
% 4.55/1.76  tff(c_1441, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_625, c_1434])).
% 4.55/1.76  tff(c_2, plain, (![A_1, B_3]: (v2_funct_1(A_1) | k2_relat_1(B_3)!=k1_relat_1(A_1) | ~v2_funct_1(k5_relat_1(B_3, A_1)) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.55/1.76  tff(c_1448, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1441, c_2])).
% 4.55/1.76  tff(c_1454, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_66, c_103, c_72, c_74, c_160, c_216, c_1448])).
% 4.55/1.76  tff(c_1456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1246, c_1454])).
% 4.55/1.76  tff(c_1458, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1238])).
% 4.55/1.76  tff(c_1459, plain, (![B_225]: (k2_funct_1('#skF_4')=B_225 | k5_relat_1(B_225, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_225)!='#skF_2' | ~v1_funct_1(B_225) | ~v1_relat_1(B_225))), inference(splitRight, [status(thm)], [c_1238])).
% 4.55/1.76  tff(c_1465, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_1459])).
% 4.55/1.76  tff(c_1472, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_160, c_1465])).
% 4.55/1.76  tff(c_1476, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1472])).
% 4.55/1.76  tff(c_1532, plain, (![C_245, E_242, A_243, D_240, F_244, B_241]: (k1_partfun1(A_243, B_241, C_245, D_240, E_242, F_244)=k5_relat_1(E_242, F_244) | ~m1_subset_1(F_244, k1_zfmisc_1(k2_zfmisc_1(C_245, D_240))) | ~v1_funct_1(F_244) | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_241))) | ~v1_funct_1(E_242))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.55/1.76  tff(c_1536, plain, (![A_243, B_241, E_242]: (k1_partfun1(A_243, B_241, '#skF_2', '#skF_1', E_242, '#skF_4')=k5_relat_1(E_242, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_241))) | ~v1_funct_1(E_242))), inference(resolution, [status(thm)], [c_62, c_1532])).
% 4.55/1.76  tff(c_1552, plain, (![A_247, B_248, E_249]: (k1_partfun1(A_247, B_248, '#skF_2', '#skF_1', E_249, '#skF_4')=k5_relat_1(E_249, '#skF_4') | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))) | ~v1_funct_1(E_249))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1536])).
% 4.55/1.76  tff(c_1561, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1552])).
% 4.55/1.76  tff(c_1568, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_625, c_1561])).
% 4.55/1.76  tff(c_1570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1476, c_1568])).
% 4.55/1.76  tff(c_1571, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1472])).
% 4.55/1.76  tff(c_1790, plain, (![A_283, C_284, B_285]: (k6_partfun1(A_283)=k5_relat_1(C_284, k2_funct_1(C_284)) | k1_xboole_0=B_285 | ~v2_funct_1(C_284) | k2_relset_1(A_283, B_285, C_284)!=B_285 | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_283, B_285))) | ~v1_funct_2(C_284, A_283, B_285) | ~v1_funct_1(C_284))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.55/1.76  tff(c_1794, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1790])).
% 4.55/1.76  tff(c_1802, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1231, c_1458, c_1571, c_1794])).
% 4.55/1.76  tff(c_1804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1229, c_1802])).
% 4.55/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.76  
% 4.55/1.76  Inference rules
% 4.55/1.76  ----------------------
% 4.55/1.76  #Ref     : 0
% 4.55/1.76  #Sup     : 372
% 4.55/1.76  #Fact    : 0
% 4.55/1.76  #Define  : 0
% 4.55/1.76  #Split   : 19
% 4.55/1.76  #Chain   : 0
% 4.55/1.76  #Close   : 0
% 4.55/1.76  
% 4.55/1.76  Ordering : KBO
% 4.55/1.76  
% 4.55/1.76  Simplification rules
% 4.55/1.76  ----------------------
% 4.55/1.76  #Subsume      : 19
% 4.55/1.76  #Demod        : 416
% 4.55/1.76  #Tautology    : 107
% 4.55/1.76  #SimpNegUnit  : 38
% 4.55/1.76  #BackRed      : 19
% 4.55/1.76  
% 4.55/1.76  #Partial instantiations: 0
% 4.55/1.76  #Strategies tried      : 1
% 4.55/1.76  
% 4.55/1.76  Timing (in seconds)
% 4.55/1.76  ----------------------
% 4.55/1.76  Preprocessing        : 0.36
% 4.55/1.76  Parsing              : 0.19
% 4.55/1.76  CNF conversion       : 0.02
% 4.55/1.76  Main loop            : 0.62
% 4.55/1.76  Inferencing          : 0.22
% 4.55/1.76  Reduction            : 0.21
% 4.55/1.77  Demodulation         : 0.15
% 4.55/1.77  BG Simplification    : 0.03
% 4.55/1.77  Subsumption          : 0.11
% 4.55/1.77  Abstraction          : 0.03
% 4.55/1.77  MUC search           : 0.00
% 4.55/1.77  Cooper               : 0.00
% 4.55/1.77  Total                : 1.03
% 4.55/1.77  Index Insertion      : 0.00
% 4.55/1.77  Index Deletion       : 0.00
% 4.55/1.77  Index Matching       : 0.00
% 4.55/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
