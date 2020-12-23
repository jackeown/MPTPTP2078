%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:25 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  170 (1469 expanded)
%              Number of leaves         :   41 ( 529 expanded)
%              Depth                    :   27
%              Number of atoms          :  431 (6094 expanded)
%              Number of equality atoms :  170 (2130 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_107,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
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

tff(f_166,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_124,axiom,(
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

tff(f_40,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_335,plain,(
    ! [C_103,E_104,D_99,F_102,A_101,B_100] :
      ( k1_partfun1(A_101,B_100,C_103,D_99,E_104,F_102) = k5_relat_1(E_104,F_102)
      | ~ m1_subset_1(F_102,k1_zfmisc_1(k2_zfmisc_1(C_103,D_99)))
      | ~ v1_funct_1(F_102)
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_1(E_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_341,plain,(
    ! [A_101,B_100,E_104] :
      ( k1_partfun1(A_101,B_100,'#skF_2','#skF_1',E_104,'#skF_4') = k5_relat_1(E_104,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_1(E_104) ) ),
    inference(resolution,[status(thm)],[c_62,c_335])).

tff(c_352,plain,(
    ! [A_109,B_110,E_111] :
      ( k1_partfun1(A_109,B_110,'#skF_2','#skF_1',E_111,'#skF_4') = k5_relat_1(E_111,'#skF_4')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_341])).

tff(c_358,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_352])).

tff(c_365,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_358])).

tff(c_30,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_195,plain,(
    ! [D_69,C_70,A_71,B_72] :
      ( D_69 = C_70
      | ~ r2_relset_1(A_71,B_72,C_70,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_203,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_195])).

tff(c_218,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_203])).

tff(c_219,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_370,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_219])).

tff(c_567,plain,(
    ! [D_127,C_122,E_123,B_124,F_126,A_125] :
      ( m1_subset_1(k1_partfun1(A_125,B_124,C_122,D_127,E_123,F_126),k1_zfmisc_1(k2_zfmisc_1(A_125,D_127)))
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_122,D_127)))
      | ~ v1_funct_1(F_126)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124)))
      | ~ v1_funct_1(E_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_609,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_567])).

tff(c_631,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_609])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_631])).

tff(c_634,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_685,plain,(
    ! [C_132,D_137,E_133,B_134,F_136,A_135] :
      ( v1_funct_1(k1_partfun1(A_135,B_134,C_132,D_137,E_133,F_136))
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_132,D_137)))
      | ~ v1_funct_1(F_136)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_691,plain,(
    ! [A_135,B_134,E_133] :
      ( v1_funct_1(k1_partfun1(A_135,B_134,'#skF_2','#skF_1',E_133,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134)))
      | ~ v1_funct_1(E_133) ) ),
    inference(resolution,[status(thm)],[c_62,c_685])).

tff(c_716,plain,(
    ! [A_141,B_142,E_143] :
      ( v1_funct_1(k1_partfun1(A_141,B_142,'#skF_2','#skF_1',E_143,'#skF_4'))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_691])).

tff(c_722,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_716])).

tff(c_729,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_634,c_722])).

tff(c_34,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_6] : k2_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    ! [A_6] : k2_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

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
    ! [A_25] :
      ( v1_relat_1(k6_partfun1(A_25))
      | ~ v1_relat_1(k2_zfmisc_1(A_25,A_25)) ) ),
    inference(resolution,[status(thm)],[c_30,c_114])).

tff(c_126,plain,(
    ! [A_25] : v1_relat_1(k6_partfun1(A_25)) ),
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
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_144,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_150,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_144])).

tff(c_157,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_150])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_relat_1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_643,plain,(
    ! [A_128,B_129] :
      ( k2_funct_1(A_128) = B_129
      | k6_partfun1(k2_relat_1(A_128)) != k5_relat_1(B_129,A_128)
      | k2_relat_1(B_129) != k1_relat_1(A_128)
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_649,plain,(
    ! [B_129] :
      ( k2_funct_1('#skF_3') = B_129
      | k5_relat_1(B_129,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_129) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_643])).

tff(c_658,plain,(
    ! [B_130] :
      ( k2_funct_1('#skF_3') = B_130
      | k5_relat_1(B_130,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_130) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_649])).

tff(c_661,plain,(
    ! [A_25] :
      ( k6_partfun1(A_25) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_25),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_25)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_126,c_658])).

tff(c_672,plain,(
    ! [A_25] :
      ( k6_partfun1(A_25) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_25),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_25
      | ~ v1_funct_1(k6_partfun1(A_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_661])).

tff(c_736,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_729,c_672])).

tff(c_739,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_810,plain,(
    ! [A_159,C_160,B_161] :
      ( k6_partfun1(A_159) = k5_relat_1(C_160,k2_funct_1(C_160))
      | k1_xboole_0 = B_161
      | ~ v2_funct_1(C_160)
      | k2_relset_1(A_159,B_161,C_160) != B_161
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_159,B_161)))
      | ~ v1_funct_2(C_160,A_159,B_161)
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_814,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_810])).

tff(c_822,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_814])).

tff(c_823,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_822])).

tff(c_14,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_partfun1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_831,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_74])).

tff(c_838,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_831])).

tff(c_870,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_77])).

tff(c_893,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_870])).

tff(c_895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_739,c_893])).

tff(c_897,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_123,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_132,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_664,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_658])).

tff(c_675,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_664])).

tff(c_676,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_675])).

tff(c_681,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_676])).

tff(c_900,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_681])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_134,plain,(
    ! [A_59,B_60,D_61] :
      ( r2_relset_1(A_59,B_60,D_61,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_141,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_158,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_144])).

tff(c_1735,plain,(
    ! [A_226,B_227,C_228,D_229] :
      ( k2_relset_1(A_226,B_227,C_228) = B_227
      | ~ r2_relset_1(B_227,B_227,k1_partfun1(B_227,A_226,A_226,B_227,D_229,C_228),k6_partfun1(B_227))
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(B_227,A_226)))
      | ~ v1_funct_2(D_229,B_227,A_226)
      | ~ v1_funct_1(D_229)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_2(C_228,A_226,B_227)
      | ~ v1_funct_1(C_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1741,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_1735])).

tff(c_1745,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_141,c_158,c_1741])).

tff(c_1747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_900,c_1745])).

tff(c_1748,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_676])).

tff(c_2877,plain,(
    ! [C_345,F_344,A_343,E_346,D_341,B_342] :
      ( k1_partfun1(A_343,B_342,C_345,D_341,E_346,F_344) = k5_relat_1(E_346,F_344)
      | ~ m1_subset_1(F_344,k1_zfmisc_1(k2_zfmisc_1(C_345,D_341)))
      | ~ v1_funct_1(F_344)
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_343,B_342)))
      | ~ v1_funct_1(E_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2883,plain,(
    ! [A_343,B_342,E_346] :
      ( k1_partfun1(A_343,B_342,'#skF_2','#skF_1',E_346,'#skF_4') = k5_relat_1(E_346,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_343,B_342)))
      | ~ v1_funct_1(E_346) ) ),
    inference(resolution,[status(thm)],[c_62,c_2877])).

tff(c_3237,plain,(
    ! [A_367,B_368,E_369] :
      ( k1_partfun1(A_367,B_368,'#skF_2','#skF_1',E_369,'#skF_4') = k5_relat_1(E_369,'#skF_4')
      | ~ m1_subset_1(E_369,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368)))
      | ~ v1_funct_1(E_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2883])).

tff(c_3243,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3237])).

tff(c_3250,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_634,c_3243])).

tff(c_1749,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_676])).

tff(c_73,plain,(
    ! [A_9,B_11] :
      ( k2_funct_1(A_9) = B_11
      | k6_partfun1(k2_relat_1(A_9)) != k5_relat_1(B_11,A_9)
      | k2_relat_1(B_11) != k1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_1753,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_73])).

tff(c_1757,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_66,c_1753])).

tff(c_1765,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1757])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_10,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_2806,plain,(
    ! [C_323,D_324,B_322,E_325,A_321] :
      ( k1_xboole_0 = C_323
      | v2_funct_1(E_325)
      | k2_relset_1(A_321,B_322,D_324) != B_322
      | ~ v2_funct_1(k1_partfun1(A_321,B_322,B_322,C_323,D_324,E_325))
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(B_322,C_323)))
      | ~ v1_funct_2(E_325,B_322,C_323)
      | ~ v1_funct_1(E_325)
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322)))
      | ~ v1_funct_2(D_324,A_321,B_322)
      | ~ v1_funct_1(D_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2814,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_634,c_2806])).

tff(c_2825,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_76,c_60,c_2814])).

tff(c_2827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1765,c_54,c_2825])).

tff(c_2829,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1757])).

tff(c_1750,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_158])).

tff(c_2940,plain,(
    ! [B_354,C_355,A_356] :
      ( k6_partfun1(B_354) = k5_relat_1(k2_funct_1(C_355),C_355)
      | k1_xboole_0 = B_354
      | ~ v2_funct_1(C_355)
      | k2_relset_1(A_356,B_354,C_355) != B_354
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_356,B_354)))
      | ~ v1_funct_2(C_355,A_356,B_354)
      | ~ v1_funct_1(C_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2946,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2940])).

tff(c_2956,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1750,c_2829,c_2946])).

tff(c_2957,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2956])).

tff(c_2977,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2957])).

tff(c_3008,plain,(
    ! [A_361,C_362,B_363] :
      ( k6_partfun1(A_361) = k5_relat_1(C_362,k2_funct_1(C_362))
      | k1_xboole_0 = B_363
      | ~ v2_funct_1(C_362)
      | k2_relset_1(A_361,B_363,C_362) != B_363
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_361,B_363)))
      | ~ v1_funct_2(C_362,A_361,B_363)
      | ~ v1_funct_1(C_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3012,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3008])).

tff(c_3020,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_3012])).

tff(c_3021,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3020])).

tff(c_3029,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3021,c_74])).

tff(c_3036,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_72,c_56,c_3029])).

tff(c_3071,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3036,c_77])).

tff(c_3096,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3071])).

tff(c_3098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2977,c_3096])).

tff(c_3100,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2957])).

tff(c_3105,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_1750])).

tff(c_3145,plain,(
    ! [A_364,C_365,B_366] :
      ( k6_partfun1(A_364) = k5_relat_1(C_365,k2_funct_1(C_365))
      | k1_xboole_0 = B_366
      | ~ v2_funct_1(C_365)
      | k2_relset_1(A_364,B_366,C_365) != B_366
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(A_364,B_366)))
      | ~ v1_funct_2(C_365,A_364,B_366)
      | ~ v1_funct_1(C_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3151,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3145])).

tff(c_3161,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3105,c_2829,c_3151])).

tff(c_3162,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3161])).

tff(c_3180,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_74])).

tff(c_3187,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_66,c_2829,c_3180])).

tff(c_3216,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3187,c_77])).

tff(c_3233,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3216])).

tff(c_2828,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_11,'#skF_4')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(splitRight,[status(thm)],[c_1757])).

tff(c_3102,plain,(
    ! [B_11] :
      ( k2_funct_1('#skF_4') = B_11
      | k5_relat_1(B_11,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_11) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_2828])).

tff(c_5623,plain,(
    ! [B_478] :
      ( k2_funct_1('#skF_4') = B_478
      | k5_relat_1(B_478,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_478) != '#skF_2'
      | ~ v1_funct_1(B_478)
      | ~ v1_relat_1(B_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3233,c_3102])).

tff(c_5719,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_5623])).

tff(c_5813,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_157,c_3250,c_5719])).

tff(c_5888,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5813,c_3162])).

tff(c_5891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1748,c_5888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.39/2.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/2.63  
% 7.39/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/2.63  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.39/2.63  
% 7.39/2.63  %Foreground sorts:
% 7.39/2.63  
% 7.39/2.63  
% 7.39/2.63  %Background operators:
% 7.39/2.63  
% 7.39/2.63  
% 7.39/2.63  %Foreground operators:
% 7.39/2.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.39/2.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.39/2.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.39/2.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.39/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.39/2.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.39/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.39/2.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.39/2.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.39/2.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.39/2.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.39/2.63  tff('#skF_2', type, '#skF_2': $i).
% 7.39/2.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.39/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.39/2.63  tff('#skF_1', type, '#skF_1': $i).
% 7.39/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.39/2.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.39/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.39/2.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.39/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.39/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.39/2.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.39/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.39/2.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.39/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.39/2.63  
% 7.39/2.66  tff(f_192, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.39/2.66  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.39/2.66  tff(f_95, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.39/2.66  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.39/2.66  tff(f_91, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.39/2.66  tff(f_107, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.39/2.66  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.39/2.66  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.39/2.66  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.39/2.66  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.39/2.66  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 7.39/2.66  tff(f_166, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.39/2.66  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.39/2.66  tff(f_124, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.39/2.66  tff(f_40, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 7.39/2.66  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.39/2.66  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_335, plain, (![C_103, E_104, D_99, F_102, A_101, B_100]: (k1_partfun1(A_101, B_100, C_103, D_99, E_104, F_102)=k5_relat_1(E_104, F_102) | ~m1_subset_1(F_102, k1_zfmisc_1(k2_zfmisc_1(C_103, D_99))) | ~v1_funct_1(F_102) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_1(E_104))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.39/2.66  tff(c_341, plain, (![A_101, B_100, E_104]: (k1_partfun1(A_101, B_100, '#skF_2', '#skF_1', E_104, '#skF_4')=k5_relat_1(E_104, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_1(E_104))), inference(resolution, [status(thm)], [c_62, c_335])).
% 7.39/2.66  tff(c_352, plain, (![A_109, B_110, E_111]: (k1_partfun1(A_109, B_110, '#skF_2', '#skF_1', E_111, '#skF_4')=k5_relat_1(E_111, '#skF_4') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_1(E_111))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_341])).
% 7.39/2.66  tff(c_358, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_352])).
% 7.39/2.66  tff(c_365, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_358])).
% 7.39/2.66  tff(c_30, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.39/2.66  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_195, plain, (![D_69, C_70, A_71, B_72]: (D_69=C_70 | ~r2_relset_1(A_71, B_72, C_70, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.39/2.66  tff(c_203, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_195])).
% 7.39/2.66  tff(c_218, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_203])).
% 7.39/2.66  tff(c_219, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_218])).
% 7.39/2.66  tff(c_370, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_219])).
% 7.39/2.66  tff(c_567, plain, (![D_127, C_122, E_123, B_124, F_126, A_125]: (m1_subset_1(k1_partfun1(A_125, B_124, C_122, D_127, E_123, F_126), k1_zfmisc_1(k2_zfmisc_1(A_125, D_127))) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_122, D_127))) | ~v1_funct_1(F_126) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))) | ~v1_funct_1(E_123))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.39/2.66  tff(c_609, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_365, c_567])).
% 7.39/2.66  tff(c_631, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_609])).
% 7.39/2.66  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_631])).
% 7.39/2.66  tff(c_634, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_218])).
% 7.39/2.66  tff(c_685, plain, (![C_132, D_137, E_133, B_134, F_136, A_135]: (v1_funct_1(k1_partfun1(A_135, B_134, C_132, D_137, E_133, F_136)) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_132, D_137))) | ~v1_funct_1(F_136) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.39/2.66  tff(c_691, plain, (![A_135, B_134, E_133]: (v1_funct_1(k1_partfun1(A_135, B_134, '#skF_2', '#skF_1', E_133, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))) | ~v1_funct_1(E_133))), inference(resolution, [status(thm)], [c_62, c_685])).
% 7.39/2.66  tff(c_716, plain, (![A_141, B_142, E_143]: (v1_funct_1(k1_partfun1(A_141, B_142, '#skF_2', '#skF_1', E_143, '#skF_4')) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(E_143))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_691])).
% 7.39/2.66  tff(c_722, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_716])).
% 7.39/2.66  tff(c_729, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_634, c_722])).
% 7.39/2.66  tff(c_34, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.39/2.66  tff(c_8, plain, (![A_6]: (k2_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.39/2.66  tff(c_77, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 7.39/2.66  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.39/2.66  tff(c_114, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.39/2.66  tff(c_117, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)) | ~v1_relat_1(k2_zfmisc_1(A_25, A_25)))), inference(resolution, [status(thm)], [c_30, c_114])).
% 7.39/2.66  tff(c_126, plain, (![A_25]: (v1_relat_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_117])).
% 7.39/2.66  tff(c_120, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_114])).
% 7.39/2.66  tff(c_129, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_120])).
% 7.39/2.66  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_144, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.39/2.66  tff(c_150, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_144])).
% 7.39/2.66  tff(c_157, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_150])).
% 7.39/2.66  tff(c_16, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_relat_1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.39/2.66  tff(c_643, plain, (![A_128, B_129]: (k2_funct_1(A_128)=B_129 | k6_partfun1(k2_relat_1(A_128))!=k5_relat_1(B_129, A_128) | k2_relat_1(B_129)!=k1_relat_1(A_128) | ~v2_funct_1(A_128) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 7.39/2.66  tff(c_649, plain, (![B_129]: (k2_funct_1('#skF_3')=B_129 | k5_relat_1(B_129, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_129)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_129) | ~v1_relat_1(B_129) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_643])).
% 7.39/2.66  tff(c_658, plain, (![B_130]: (k2_funct_1('#skF_3')=B_130 | k5_relat_1(B_130, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_130)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_130) | ~v1_relat_1(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_649])).
% 7.39/2.66  tff(c_661, plain, (![A_25]: (k6_partfun1(A_25)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_25), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_25))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_126, c_658])).
% 7.39/2.66  tff(c_672, plain, (![A_25]: (k6_partfun1(A_25)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_25), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_25 | ~v1_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_661])).
% 7.39/2.66  tff(c_736, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_729, c_672])).
% 7.39/2.66  tff(c_739, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_736])).
% 7.39/2.66  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_810, plain, (![A_159, C_160, B_161]: (k6_partfun1(A_159)=k5_relat_1(C_160, k2_funct_1(C_160)) | k1_xboole_0=B_161 | ~v2_funct_1(C_160) | k2_relset_1(A_159, B_161, C_160)!=B_161 | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_159, B_161))) | ~v1_funct_2(C_160, A_159, B_161) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.39/2.66  tff(c_814, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_810])).
% 7.39/2.66  tff(c_822, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_814])).
% 7.39/2.66  tff(c_823, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_822])).
% 7.39/2.66  tff(c_14, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.39/2.66  tff(c_74, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_partfun1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 7.39/2.66  tff(c_831, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_823, c_74])).
% 7.39/2.66  tff(c_838, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_831])).
% 7.39/2.66  tff(c_870, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_838, c_77])).
% 7.39/2.66  tff(c_893, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_870])).
% 7.39/2.66  tff(c_895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_739, c_893])).
% 7.39/2.66  tff(c_897, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_736])).
% 7.39/2.66  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_123, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_114])).
% 7.39/2.66  tff(c_132, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 7.39/2.66  tff(c_664, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_658])).
% 7.39/2.66  tff(c_675, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_664])).
% 7.39/2.66  tff(c_676, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_675])).
% 7.39/2.66  tff(c_681, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_676])).
% 7.39/2.66  tff(c_900, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_897, c_681])).
% 7.39/2.66  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_134, plain, (![A_59, B_60, D_61]: (r2_relset_1(A_59, B_60, D_61, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.39/2.66  tff(c_141, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_30, c_134])).
% 7.39/2.66  tff(c_158, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_144])).
% 7.39/2.66  tff(c_1735, plain, (![A_226, B_227, C_228, D_229]: (k2_relset_1(A_226, B_227, C_228)=B_227 | ~r2_relset_1(B_227, B_227, k1_partfun1(B_227, A_226, A_226, B_227, D_229, C_228), k6_partfun1(B_227)) | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(B_227, A_226))) | ~v1_funct_2(D_229, B_227, A_226) | ~v1_funct_1(D_229) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_2(C_228, A_226, B_227) | ~v1_funct_1(C_228))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.39/2.66  tff(c_1741, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_634, c_1735])).
% 7.39/2.66  tff(c_1745, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_141, c_158, c_1741])).
% 7.39/2.66  tff(c_1747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_900, c_1745])).
% 7.39/2.66  tff(c_1748, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_676])).
% 7.39/2.66  tff(c_2877, plain, (![C_345, F_344, A_343, E_346, D_341, B_342]: (k1_partfun1(A_343, B_342, C_345, D_341, E_346, F_344)=k5_relat_1(E_346, F_344) | ~m1_subset_1(F_344, k1_zfmisc_1(k2_zfmisc_1(C_345, D_341))) | ~v1_funct_1(F_344) | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_343, B_342))) | ~v1_funct_1(E_346))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.39/2.66  tff(c_2883, plain, (![A_343, B_342, E_346]: (k1_partfun1(A_343, B_342, '#skF_2', '#skF_1', E_346, '#skF_4')=k5_relat_1(E_346, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_343, B_342))) | ~v1_funct_1(E_346))), inference(resolution, [status(thm)], [c_62, c_2877])).
% 7.39/2.66  tff(c_3237, plain, (![A_367, B_368, E_369]: (k1_partfun1(A_367, B_368, '#skF_2', '#skF_1', E_369, '#skF_4')=k5_relat_1(E_369, '#skF_4') | ~m1_subset_1(E_369, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))) | ~v1_funct_1(E_369))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2883])).
% 7.39/2.66  tff(c_3243, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3237])).
% 7.39/2.66  tff(c_3250, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_634, c_3243])).
% 7.39/2.66  tff(c_1749, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_676])).
% 7.39/2.66  tff(c_73, plain, (![A_9, B_11]: (k2_funct_1(A_9)=B_11 | k6_partfun1(k2_relat_1(A_9))!=k5_relat_1(B_11, A_9) | k2_relat_1(B_11)!=k1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 7.39/2.66  tff(c_1753, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1749, c_73])).
% 7.39/2.66  tff(c_1757, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_66, c_1753])).
% 7.39/2.66  tff(c_1765, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1757])).
% 7.39/2.66  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.39/2.66  tff(c_10, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.39/2.66  tff(c_76, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 7.39/2.66  tff(c_2806, plain, (![C_323, D_324, B_322, E_325, A_321]: (k1_xboole_0=C_323 | v2_funct_1(E_325) | k2_relset_1(A_321, B_322, D_324)!=B_322 | ~v2_funct_1(k1_partfun1(A_321, B_322, B_322, C_323, D_324, E_325)) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(B_322, C_323))) | ~v1_funct_2(E_325, B_322, C_323) | ~v1_funct_1(E_325) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))) | ~v1_funct_2(D_324, A_321, B_322) | ~v1_funct_1(D_324))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.39/2.66  tff(c_2814, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_634, c_2806])).
% 7.39/2.66  tff(c_2825, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_76, c_60, c_2814])).
% 7.39/2.66  tff(c_2827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1765, c_54, c_2825])).
% 7.39/2.66  tff(c_2829, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1757])).
% 7.39/2.66  tff(c_1750, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_158])).
% 7.39/2.66  tff(c_2940, plain, (![B_354, C_355, A_356]: (k6_partfun1(B_354)=k5_relat_1(k2_funct_1(C_355), C_355) | k1_xboole_0=B_354 | ~v2_funct_1(C_355) | k2_relset_1(A_356, B_354, C_355)!=B_354 | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_356, B_354))) | ~v1_funct_2(C_355, A_356, B_354) | ~v1_funct_1(C_355))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.39/2.66  tff(c_2946, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2940])).
% 7.39/2.66  tff(c_2956, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1750, c_2829, c_2946])).
% 7.39/2.66  tff(c_2957, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_2956])).
% 7.39/2.66  tff(c_2977, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2957])).
% 7.39/2.66  tff(c_3008, plain, (![A_361, C_362, B_363]: (k6_partfun1(A_361)=k5_relat_1(C_362, k2_funct_1(C_362)) | k1_xboole_0=B_363 | ~v2_funct_1(C_362) | k2_relset_1(A_361, B_363, C_362)!=B_363 | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_361, B_363))) | ~v1_funct_2(C_362, A_361, B_363) | ~v1_funct_1(C_362))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.39/2.66  tff(c_3012, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3008])).
% 7.39/2.66  tff(c_3020, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_3012])).
% 7.39/2.66  tff(c_3021, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_3020])).
% 7.39/2.66  tff(c_3029, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3021, c_74])).
% 7.39/2.66  tff(c_3036, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_72, c_56, c_3029])).
% 7.39/2.66  tff(c_3071, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3036, c_77])).
% 7.39/2.66  tff(c_3096, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3071])).
% 7.39/2.66  tff(c_3098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2977, c_3096])).
% 7.39/2.66  tff(c_3100, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2957])).
% 7.39/2.66  tff(c_3105, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_1750])).
% 7.39/2.66  tff(c_3145, plain, (![A_364, C_365, B_366]: (k6_partfun1(A_364)=k5_relat_1(C_365, k2_funct_1(C_365)) | k1_xboole_0=B_366 | ~v2_funct_1(C_365) | k2_relset_1(A_364, B_366, C_365)!=B_366 | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(A_364, B_366))) | ~v1_funct_2(C_365, A_364, B_366) | ~v1_funct_1(C_365))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.39/2.66  tff(c_3151, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3145])).
% 7.39/2.66  tff(c_3161, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3105, c_2829, c_3151])).
% 7.39/2.66  tff(c_3162, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_3161])).
% 7.39/2.66  tff(c_3180, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3162, c_74])).
% 7.39/2.66  tff(c_3187, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_66, c_2829, c_3180])).
% 7.39/2.66  tff(c_3216, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3187, c_77])).
% 7.39/2.66  tff(c_3233, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3216])).
% 7.39/2.66  tff(c_2828, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_11, '#skF_4') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(splitRight, [status(thm)], [c_1757])).
% 7.39/2.66  tff(c_3102, plain, (![B_11]: (k2_funct_1('#skF_4')=B_11 | k5_relat_1(B_11, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_11)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_2828])).
% 7.39/2.66  tff(c_5623, plain, (![B_478]: (k2_funct_1('#skF_4')=B_478 | k5_relat_1(B_478, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_478)!='#skF_2' | ~v1_funct_1(B_478) | ~v1_relat_1(B_478))), inference(demodulation, [status(thm), theory('equality')], [c_3233, c_3102])).
% 7.39/2.66  tff(c_5719, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_5623])).
% 7.39/2.66  tff(c_5813, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_157, c_3250, c_5719])).
% 7.39/2.66  tff(c_5888, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5813, c_3162])).
% 7.39/2.66  tff(c_5891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1748, c_5888])).
% 7.39/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/2.66  
% 7.39/2.66  Inference rules
% 7.39/2.66  ----------------------
% 7.39/2.66  #Ref     : 0
% 7.39/2.66  #Sup     : 1207
% 7.39/2.66  #Fact    : 0
% 7.39/2.66  #Define  : 0
% 7.39/2.66  #Split   : 32
% 7.39/2.66  #Chain   : 0
% 7.39/2.66  #Close   : 0
% 7.39/2.66  
% 7.39/2.66  Ordering : KBO
% 7.39/2.66  
% 7.39/2.66  Simplification rules
% 7.39/2.66  ----------------------
% 7.39/2.66  #Subsume      : 99
% 7.39/2.66  #Demod        : 2221
% 7.39/2.66  #Tautology    : 328
% 7.39/2.66  #SimpNegUnit  : 155
% 7.39/2.66  #BackRed      : 54
% 7.39/2.66  
% 7.39/2.66  #Partial instantiations: 0
% 7.39/2.66  #Strategies tried      : 1
% 7.39/2.66  
% 7.39/2.66  Timing (in seconds)
% 7.39/2.66  ----------------------
% 7.65/2.66  Preprocessing        : 0.37
% 7.65/2.66  Parsing              : 0.19
% 7.65/2.66  CNF conversion       : 0.03
% 7.65/2.66  Main loop            : 1.51
% 7.65/2.66  Inferencing          : 0.46
% 7.65/2.66  Reduction            : 0.65
% 7.65/2.66  Demodulation         : 0.50
% 7.65/2.66  BG Simplification    : 0.05
% 7.65/2.66  Subsumption          : 0.25
% 7.65/2.66  Abstraction          : 0.07
% 7.65/2.66  MUC search           : 0.00
% 7.65/2.66  Cooper               : 0.00
% 7.65/2.66  Total                : 1.92
% 7.65/2.66  Index Insertion      : 0.00
% 7.65/2.66  Index Deletion       : 0.00
% 7.65/2.66  Index Matching       : 0.00
% 7.65/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
