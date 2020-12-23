%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:20 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 764 expanded)
%              Number of leaves         :   41 ( 288 expanded)
%              Depth                    :   18
%              Number of atoms          :  309 (3138 expanded)
%              Number of equality atoms :  111 (1131 expanded)
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

tff(f_183,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_140,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_80,axiom,(
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

tff(f_98,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_157,axiom,(
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

tff(f_53,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_51,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_94,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_94])).

tff(c_109,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_103,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_94])).

tff(c_112,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_157,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_169,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_157])).

tff(c_228,plain,(
    ! [B_76,A_77,C_78] :
      ( k1_xboole_0 = B_76
      | k1_relset_1(A_77,B_76,C_78) = A_77
      | ~ v1_funct_2(C_78,A_77,B_76)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_237,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_228])).

tff(c_246,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_169,c_237])).

tff(c_247,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_246])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_125,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_134,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_138,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_134])).

tff(c_46,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_relat_1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_526,plain,(
    ! [A_129,B_130] :
      ( k2_funct_1(A_129) = B_130
      | k6_partfun1(k2_relat_1(A_129)) != k5_relat_1(B_130,A_129)
      | k2_relat_1(B_130) != k1_relat_1(A_129)
      | ~ v2_funct_1(A_129)
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_532,plain,(
    ! [B_130] :
      ( k2_funct_1('#skF_3') = B_130
      | k5_relat_1(B_130,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_130) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_526])).

tff(c_537,plain,(
    ! [B_131] :
      ( k2_funct_1('#skF_3') = B_131
      | k5_relat_1(B_131,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_131) != '#skF_1'
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_72,c_56,c_247,c_532])).

tff(c_546,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_537])).

tff(c_556,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_546])).

tff(c_557,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_556])).

tff(c_559,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_26,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_73,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_26])).

tff(c_114,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_121,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_73,c_114])).

tff(c_136,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_125])).

tff(c_462,plain,(
    ! [C_126,F_123,E_124,B_127,A_125,D_128] :
      ( m1_subset_1(k1_partfun1(A_125,B_127,C_126,D_128,E_124,F_123),k1_zfmisc_1(k2_zfmisc_1(A_125,D_128)))
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_126,D_128)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_127)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_317,plain,(
    ! [D_88,C_89,A_90,B_91] :
      ( D_88 = C_89
      | ~ r2_relset_1(A_90,B_91,C_89,D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_325,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_317])).

tff(c_340,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_325])).

tff(c_343,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_478,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_462,c_343])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_478])).

tff(c_517,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_892,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( k2_relset_1(A_163,B_164,C_165) = B_164
      | ~ r2_relset_1(B_164,B_164,k1_partfun1(B_164,A_163,A_163,B_164,D_166,C_165),k6_partfun1(B_164))
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(B_164,A_163)))
      | ~ v1_funct_2(D_166,B_164,A_163)
      | ~ v1_funct_1(D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_2(C_165,A_163,B_164)
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_895,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_892])).

tff(c_897,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_121,c_136,c_895])).

tff(c_899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_897])).

tff(c_900,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_168,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_157])).

tff(c_234,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_228])).

tff(c_242,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_168,c_234])).

tff(c_243,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_242])).

tff(c_901,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_74,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_partfun1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_905,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_74])).

tff(c_909,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_66,c_243,c_905])).

tff(c_917,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_909])).

tff(c_10,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_974,plain,(
    ! [B_188,C_189,D_185,E_187,A_184,F_186] :
      ( k1_partfun1(A_184,B_188,C_189,D_185,E_187,F_186) = k5_relat_1(E_187,F_186)
      | ~ m1_subset_1(F_186,k1_zfmisc_1(k2_zfmisc_1(C_189,D_185)))
      | ~ v1_funct_1(F_186)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_184,B_188)))
      | ~ v1_funct_1(E_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_978,plain,(
    ! [A_184,B_188,E_187] :
      ( k1_partfun1(A_184,B_188,'#skF_2','#skF_1',E_187,'#skF_4') = k5_relat_1(E_187,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_184,B_188)))
      | ~ v1_funct_1(E_187) ) ),
    inference(resolution,[status(thm)],[c_62,c_974])).

tff(c_1329,plain,(
    ! [A_204,B_205,E_206] :
      ( k1_partfun1(A_204,B_205,'#skF_2','#skF_1',E_206,'#skF_4') = k5_relat_1(E_206,'#skF_4')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(E_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_978])).

tff(c_1350,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1329])).

tff(c_1367,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_517,c_1350])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( v2_funct_1(A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(k5_relat_1(B_8,A_6))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1374,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1367,c_6])).

tff(c_1380,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_66,c_112,c_72,c_77,c_138,c_243,c_1374])).

tff(c_1382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_917,c_1380])).

tff(c_1384,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_909])).

tff(c_1385,plain,(
    ! [B_207] :
      ( k2_funct_1('#skF_4') = B_207
      | k5_relat_1(B_207,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_207) != '#skF_2'
      | ~ v1_funct_1(B_207)
      | ~ v1_relat_1(B_207) ) ),
    inference(splitRight,[status(thm)],[c_909])).

tff(c_1391,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_1385])).

tff(c_1401,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_138,c_1391])).

tff(c_1406,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1401])).

tff(c_1424,plain,(
    ! [D_220,F_221,E_222,C_224,A_219,B_223] :
      ( k1_partfun1(A_219,B_223,C_224,D_220,E_222,F_221) = k5_relat_1(E_222,F_221)
      | ~ m1_subset_1(F_221,k1_zfmisc_1(k2_zfmisc_1(C_224,D_220)))
      | ~ v1_funct_1(F_221)
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_219,B_223)))
      | ~ v1_funct_1(E_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1428,plain,(
    ! [A_219,B_223,E_222] :
      ( k1_partfun1(A_219,B_223,'#skF_2','#skF_1',E_222,'#skF_4') = k5_relat_1(E_222,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(A_219,B_223)))
      | ~ v1_funct_1(E_222) ) ),
    inference(resolution,[status(thm)],[c_62,c_1424])).

tff(c_1544,plain,(
    ! [A_239,B_240,E_241] :
      ( k1_partfun1(A_239,B_240,'#skF_2','#skF_1',E_241,'#skF_4') = k5_relat_1(E_241,'#skF_4')
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240)))
      | ~ v1_funct_1(E_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1428])).

tff(c_1556,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1544])).

tff(c_1564,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_517,c_1556])).

tff(c_1566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1406,c_1564])).

tff(c_1567,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1401])).

tff(c_14,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_relat_1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_75,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k2_funct_1(A_10)) = k6_partfun1(k1_relat_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_1579,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1567,c_75])).

tff(c_1590,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_66,c_1384,c_243,c_1579])).

tff(c_1592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_900,c_1590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:41:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/1.83  
% 4.75/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.83  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.79/1.83  
% 4.79/1.83  %Foreground sorts:
% 4.79/1.83  
% 4.79/1.83  
% 4.79/1.83  %Background operators:
% 4.79/1.83  
% 4.79/1.83  
% 4.79/1.83  %Foreground operators:
% 4.79/1.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.79/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.79/1.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.79/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.79/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.79/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.79/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.79/1.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.79/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.79/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.79/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.79/1.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.79/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.79/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.79/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.79/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.79/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.79/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.83  
% 4.79/1.86  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.79/1.86  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.79/1.86  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.79/1.86  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.79/1.86  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.79/1.86  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.79/1.86  tff(f_140, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.79/1.86  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.79/1.86  tff(f_98, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.79/1.86  tff(f_96, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.79/1.86  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.79/1.86  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.79/1.86  tff(f_53, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 4.79/1.86  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.79/1.86  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.79/1.86  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.79/1.86  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.79/1.86  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_94, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.79/1.86  tff(c_100, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_94])).
% 4.79/1.86  tff(c_109, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 4.79/1.86  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_103, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_94])).
% 4.79/1.86  tff(c_112, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_103])).
% 4.79/1.86  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_157, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.79/1.86  tff(c_169, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_157])).
% 4.79/1.86  tff(c_228, plain, (![B_76, A_77, C_78]: (k1_xboole_0=B_76 | k1_relset_1(A_77, B_76, C_78)=A_77 | ~v1_funct_2(C_78, A_77, B_76) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.79/1.86  tff(c_237, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_228])).
% 4.79/1.86  tff(c_246, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_169, c_237])).
% 4.79/1.86  tff(c_247, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_246])).
% 4.79/1.86  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_125, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.79/1.86  tff(c_134, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_125])).
% 4.79/1.86  tff(c_138, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_134])).
% 4.79/1.86  tff(c_46, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.79/1.86  tff(c_16, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_relat_1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.79/1.86  tff(c_526, plain, (![A_129, B_130]: (k2_funct_1(A_129)=B_130 | k6_partfun1(k2_relat_1(A_129))!=k5_relat_1(B_130, A_129) | k2_relat_1(B_130)!=k1_relat_1(A_129) | ~v2_funct_1(A_129) | ~v1_funct_1(B_130) | ~v1_relat_1(B_130) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 4.79/1.86  tff(c_532, plain, (![B_130]: (k2_funct_1('#skF_3')=B_130 | k5_relat_1(B_130, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_130)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_130) | ~v1_relat_1(B_130) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_526])).
% 4.79/1.86  tff(c_537, plain, (![B_131]: (k2_funct_1('#skF_3')=B_131 | k5_relat_1(B_131, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_131)!='#skF_1' | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_72, c_56, c_247, c_532])).
% 4.79/1.86  tff(c_546, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_109, c_537])).
% 4.79/1.86  tff(c_556, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_546])).
% 4.79/1.86  tff(c_557, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_556])).
% 4.79/1.86  tff(c_559, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_557])).
% 4.79/1.86  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_26, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.79/1.86  tff(c_73, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_26])).
% 4.79/1.86  tff(c_114, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.79/1.86  tff(c_121, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_73, c_114])).
% 4.79/1.86  tff(c_136, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_125])).
% 4.79/1.86  tff(c_462, plain, (![C_126, F_123, E_124, B_127, A_125, D_128]: (m1_subset_1(k1_partfun1(A_125, B_127, C_126, D_128, E_124, F_123), k1_zfmisc_1(k2_zfmisc_1(A_125, D_128))) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_126, D_128))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_127))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.79/1.86  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_317, plain, (![D_88, C_89, A_90, B_91]: (D_88=C_89 | ~r2_relset_1(A_90, B_91, C_89, D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.79/1.86  tff(c_325, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_317])).
% 4.79/1.86  tff(c_340, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_325])).
% 4.79/1.86  tff(c_343, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_340])).
% 4.79/1.86  tff(c_478, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_462, c_343])).
% 4.79/1.86  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_478])).
% 4.79/1.86  tff(c_517, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_340])).
% 4.79/1.86  tff(c_892, plain, (![A_163, B_164, C_165, D_166]: (k2_relset_1(A_163, B_164, C_165)=B_164 | ~r2_relset_1(B_164, B_164, k1_partfun1(B_164, A_163, A_163, B_164, D_166, C_165), k6_partfun1(B_164)) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(B_164, A_163))) | ~v1_funct_2(D_166, B_164, A_163) | ~v1_funct_1(D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_2(C_165, A_163, B_164) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.79/1.86  tff(c_895, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_517, c_892])).
% 4.79/1.86  tff(c_897, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_121, c_136, c_895])).
% 4.79/1.86  tff(c_899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_897])).
% 4.79/1.86  tff(c_900, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_557])).
% 4.79/1.86  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.79/1.86  tff(c_168, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_157])).
% 4.79/1.86  tff(c_234, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_228])).
% 4.79/1.86  tff(c_242, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_168, c_234])).
% 4.79/1.86  tff(c_243, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_242])).
% 4.79/1.86  tff(c_901, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_557])).
% 4.79/1.86  tff(c_74, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_partfun1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 4.79/1.86  tff(c_905, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_901, c_74])).
% 4.79/1.86  tff(c_909, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_66, c_243, c_905])).
% 4.79/1.86  tff(c_917, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_909])).
% 4.79/1.86  tff(c_10, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.79/1.86  tff(c_77, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 4.79/1.86  tff(c_974, plain, (![B_188, C_189, D_185, E_187, A_184, F_186]: (k1_partfun1(A_184, B_188, C_189, D_185, E_187, F_186)=k5_relat_1(E_187, F_186) | ~m1_subset_1(F_186, k1_zfmisc_1(k2_zfmisc_1(C_189, D_185))) | ~v1_funct_1(F_186) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_184, B_188))) | ~v1_funct_1(E_187))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.79/1.86  tff(c_978, plain, (![A_184, B_188, E_187]: (k1_partfun1(A_184, B_188, '#skF_2', '#skF_1', E_187, '#skF_4')=k5_relat_1(E_187, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_184, B_188))) | ~v1_funct_1(E_187))), inference(resolution, [status(thm)], [c_62, c_974])).
% 4.79/1.86  tff(c_1329, plain, (![A_204, B_205, E_206]: (k1_partfun1(A_204, B_205, '#skF_2', '#skF_1', E_206, '#skF_4')=k5_relat_1(E_206, '#skF_4') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(E_206))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_978])).
% 4.79/1.86  tff(c_1350, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1329])).
% 4.79/1.86  tff(c_1367, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_517, c_1350])).
% 4.79/1.86  tff(c_6, plain, (![A_6, B_8]: (v2_funct_1(A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(k5_relat_1(B_8, A_6)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.79/1.86  tff(c_1374, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1367, c_6])).
% 4.79/1.86  tff(c_1380, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_66, c_112, c_72, c_77, c_138, c_243, c_1374])).
% 4.79/1.86  tff(c_1382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_917, c_1380])).
% 4.79/1.86  tff(c_1384, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_909])).
% 4.79/1.86  tff(c_1385, plain, (![B_207]: (k2_funct_1('#skF_4')=B_207 | k5_relat_1(B_207, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_207)!='#skF_2' | ~v1_funct_1(B_207) | ~v1_relat_1(B_207))), inference(splitRight, [status(thm)], [c_909])).
% 4.79/1.86  tff(c_1391, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_1385])).
% 4.79/1.86  tff(c_1401, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_138, c_1391])).
% 4.79/1.86  tff(c_1406, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1401])).
% 4.79/1.86  tff(c_1424, plain, (![D_220, F_221, E_222, C_224, A_219, B_223]: (k1_partfun1(A_219, B_223, C_224, D_220, E_222, F_221)=k5_relat_1(E_222, F_221) | ~m1_subset_1(F_221, k1_zfmisc_1(k2_zfmisc_1(C_224, D_220))) | ~v1_funct_1(F_221) | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_219, B_223))) | ~v1_funct_1(E_222))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.79/1.86  tff(c_1428, plain, (![A_219, B_223, E_222]: (k1_partfun1(A_219, B_223, '#skF_2', '#skF_1', E_222, '#skF_4')=k5_relat_1(E_222, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(A_219, B_223))) | ~v1_funct_1(E_222))), inference(resolution, [status(thm)], [c_62, c_1424])).
% 4.79/1.86  tff(c_1544, plain, (![A_239, B_240, E_241]: (k1_partfun1(A_239, B_240, '#skF_2', '#skF_1', E_241, '#skF_4')=k5_relat_1(E_241, '#skF_4') | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))) | ~v1_funct_1(E_241))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1428])).
% 4.79/1.86  tff(c_1556, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1544])).
% 4.79/1.86  tff(c_1564, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_517, c_1556])).
% 4.79/1.86  tff(c_1566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1406, c_1564])).
% 4.79/1.86  tff(c_1567, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1401])).
% 4.79/1.86  tff(c_14, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_relat_1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.79/1.86  tff(c_75, plain, (![A_10]: (k5_relat_1(A_10, k2_funct_1(A_10))=k6_partfun1(k1_relat_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 4.79/1.86  tff(c_1579, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1567, c_75])).
% 4.79/1.86  tff(c_1590, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_66, c_1384, c_243, c_1579])).
% 4.79/1.86  tff(c_1592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_900, c_1590])).
% 4.79/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.86  
% 4.79/1.86  Inference rules
% 4.79/1.86  ----------------------
% 4.79/1.86  #Ref     : 0
% 4.79/1.86  #Sup     : 320
% 4.79/1.86  #Fact    : 0
% 4.79/1.86  #Define  : 0
% 4.79/1.86  #Split   : 16
% 4.79/1.86  #Chain   : 0
% 4.79/1.86  #Close   : 0
% 4.79/1.86  
% 4.79/1.86  Ordering : KBO
% 4.79/1.86  
% 4.79/1.86  Simplification rules
% 4.79/1.86  ----------------------
% 4.79/1.86  #Subsume      : 2
% 4.79/1.86  #Demod        : 273
% 4.79/1.86  #Tautology    : 79
% 4.79/1.86  #SimpNegUnit  : 21
% 4.79/1.86  #BackRed      : 9
% 4.79/1.86  
% 4.79/1.86  #Partial instantiations: 0
% 4.79/1.86  #Strategies tried      : 1
% 4.79/1.86  
% 4.79/1.86  Timing (in seconds)
% 4.79/1.86  ----------------------
% 4.79/1.86  Preprocessing        : 0.41
% 4.79/1.86  Parsing              : 0.20
% 4.79/1.86  CNF conversion       : 0.03
% 4.79/1.86  Main loop            : 0.66
% 4.79/1.86  Inferencing          : 0.25
% 4.79/1.86  Reduction            : 0.21
% 4.79/1.86  Demodulation         : 0.15
% 4.79/1.86  BG Simplification    : 0.03
% 4.79/1.86  Subsumption          : 0.11
% 4.79/1.86  Abstraction          : 0.03
% 4.79/1.86  MUC search           : 0.00
% 4.79/1.86  Cooper               : 0.00
% 4.79/1.86  Total                : 1.12
% 4.79/1.86  Index Insertion      : 0.00
% 4.79/1.86  Index Deletion       : 0.00
% 4.79/1.86  Index Matching       : 0.00
% 4.79/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
