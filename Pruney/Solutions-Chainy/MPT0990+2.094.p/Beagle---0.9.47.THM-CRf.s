%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:10 EST 2020

% Result     : Theorem 7.35s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  160 (1094 expanded)
%              Number of leaves         :   40 ( 401 expanded)
%              Depth                    :   21
%              Number of atoms          :  411 (4690 expanded)
%              Number of equality atoms :  155 (1653 expanded)
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

tff(f_187,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_102,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
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

tff(f_161,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_119,axiom,(
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

tff(f_31,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_145,axiom,(
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

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_276,plain,(
    ! [C_85,E_87,F_88,A_89,B_86,D_90] :
      ( k1_partfun1(A_89,B_86,C_85,D_90,E_87,F_88) = k5_relat_1(E_87,F_88)
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_85,D_90)))
      | ~ v1_funct_1(F_88)
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_282,plain,(
    ! [A_89,B_86,E_87] :
      ( k1_partfun1(A_89,B_86,'#skF_2','#skF_1',E_87,'#skF_4') = k5_relat_1(E_87,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(resolution,[status(thm)],[c_60,c_276])).

tff(c_365,plain,(
    ! [A_103,B_104,E_105] :
      ( k1_partfun1(A_103,B_104,'#skF_2','#skF_1',E_105,'#skF_4') = k5_relat_1(E_105,'#skF_4')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_282])).

tff(c_371,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_365])).

tff(c_378,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_371])).

tff(c_28,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_184,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r2_relset_1(A_68,B_69,C_67,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_192,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_184])).

tff(c_207,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_192])).

tff(c_208,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_383,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_208])).

tff(c_440,plain,(
    ! [B_111,A_110,F_112,C_109,D_113,E_114] :
      ( m1_subset_1(k1_partfun1(A_110,B_111,C_109,D_113,E_114,F_112),k1_zfmisc_1(k2_zfmisc_1(A_110,D_113)))
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_109,D_113)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_474,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_440])).

tff(c_495,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_474])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_383,c_495])).

tff(c_498,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_541,plain,(
    ! [B_121,D_123,A_120,C_119,E_124,F_122] :
      ( v1_funct_1(k1_partfun1(A_120,B_121,C_119,D_123,E_124,F_122))
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_119,D_123)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_547,plain,(
    ! [A_120,B_121,E_124] :
      ( v1_funct_1(k1_partfun1(A_120,B_121,'#skF_2','#skF_1',E_124,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(E_124) ) ),
    inference(resolution,[status(thm)],[c_60,c_541])).

tff(c_572,plain,(
    ! [A_128,B_129,E_130] :
      ( v1_funct_1(k1_partfun1(A_128,B_129,'#skF_2','#skF_1',E_130,'#skF_4'))
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_547])).

tff(c_578,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_572])).

tff(c_585,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_498,c_578])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4])).

tff(c_109,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_119,plain,(
    ! [A_23] : v1_relat_1(k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_28,c_109])).

tff(c_120,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_109])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_133,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_139,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_133])).

tff(c_146,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_139])).

tff(c_12,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_relat_1(k2_relat_1(A_4)) != k5_relat_1(B_6,A_4)
      | k2_relat_1(B_6) != k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_507,plain,(
    ! [A_115,B_116] :
      ( k2_funct_1(A_115) = B_116
      | k6_partfun1(k2_relat_1(A_115)) != k5_relat_1(B_116,A_115)
      | k2_relat_1(B_116) != k1_relat_1(A_115)
      | ~ v2_funct_1(A_115)
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_511,plain,(
    ! [B_116] :
      ( k2_funct_1('#skF_3') = B_116
      | k5_relat_1(B_116,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_116) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_507])).

tff(c_518,plain,(
    ! [B_117] :
      ( k2_funct_1('#skF_3') = B_117
      | k5_relat_1(B_117,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_117) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_70,c_54,c_511])).

tff(c_521,plain,(
    ! [A_23] :
      ( k6_partfun1(A_23) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_23),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_23)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_119,c_518])).

tff(c_529,plain,(
    ! [A_23] :
      ( k6_partfun1(A_23) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_23),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_23
      | ~ v1_funct_1(k6_partfun1(A_23)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_521])).

tff(c_592,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_585,c_529])).

tff(c_595,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_650,plain,(
    ! [A_143,C_144,B_145] :
      ( k6_partfun1(A_143) = k5_relat_1(C_144,k2_funct_1(C_144))
      | k1_xboole_0 = B_145
      | ~ v2_funct_1(C_144)
      | k2_relset_1(A_143,B_145,C_144) != B_145
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_143,B_145)))
      | ~ v1_funct_2(C_144,A_143,B_145)
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_654,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_650])).

tff(c_662,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_654])).

tff(c_663,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_662])).

tff(c_8,plain,(
    ! [A_3] :
      ( k2_relat_1(k5_relat_1(A_3,k2_funct_1(A_3))) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_671,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_8])).

tff(c_678,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_70,c_54,c_73,c_671])).

tff(c_680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_678])).

tff(c_682,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_121,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_109])).

tff(c_524,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_518])).

tff(c_532,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_524])).

tff(c_533,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_532])).

tff(c_537,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_685,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_537])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_123,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_130,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_28,c_123])).

tff(c_147,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_133])).

tff(c_1358,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k2_relset_1(A_196,B_197,C_198) = B_197
      | ~ r2_relset_1(B_197,B_197,k1_partfun1(B_197,A_196,A_196,B_197,D_199,C_198),k6_partfun1(B_197))
      | ~ m1_subset_1(D_199,k1_zfmisc_1(k2_zfmisc_1(B_197,A_196)))
      | ~ v1_funct_2(D_199,B_197,A_196)
      | ~ v1_funct_1(D_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_2(C_198,A_196,B_197)
      | ~ v1_funct_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1364,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_1358])).

tff(c_1368,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_130,c_147,c_1364])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_1368])).

tff(c_1371,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_2484,plain,(
    ! [A_317,F_316,C_313,B_314,E_315,D_318] :
      ( k1_partfun1(A_317,B_314,C_313,D_318,E_315,F_316) = k5_relat_1(E_315,F_316)
      | ~ m1_subset_1(F_316,k1_zfmisc_1(k2_zfmisc_1(C_313,D_318)))
      | ~ v1_funct_1(F_316)
      | ~ m1_subset_1(E_315,k1_zfmisc_1(k2_zfmisc_1(A_317,B_314)))
      | ~ v1_funct_1(E_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2490,plain,(
    ! [A_317,B_314,E_315] :
      ( k1_partfun1(A_317,B_314,'#skF_2','#skF_1',E_315,'#skF_4') = k5_relat_1(E_315,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_315,k1_zfmisc_1(k2_zfmisc_1(A_317,B_314)))
      | ~ v1_funct_1(E_315) ) ),
    inference(resolution,[status(thm)],[c_60,c_2484])).

tff(c_2503,plain,(
    ! [A_320,B_321,E_322] :
      ( k1_partfun1(A_320,B_321,'#skF_2','#skF_1',E_322,'#skF_4') = k5_relat_1(E_322,'#skF_4')
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321)))
      | ~ v1_funct_1(E_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2490])).

tff(c_2509,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2503])).

tff(c_2516,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_498,c_2509])).

tff(c_1372,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_71,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_partfun1(k2_relat_1(A_4)) != k5_relat_1(B_6,A_4)
      | k2_relat_1(B_6) != k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_1376,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1372,c_71])).

tff(c_1380,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_64,c_1376])).

tff(c_1388,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1380])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_6,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_2409,plain,(
    ! [C_296,D_294,E_293,A_292,B_295] :
      ( k1_xboole_0 = C_296
      | v2_funct_1(E_293)
      | k2_relset_1(A_292,B_295,D_294) != B_295
      | ~ v2_funct_1(k1_partfun1(A_292,B_295,B_295,C_296,D_294,E_293))
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(B_295,C_296)))
      | ~ v1_funct_2(E_293,B_295,C_296)
      | ~ v1_funct_1(E_293)
      | ~ m1_subset_1(D_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_295)))
      | ~ v1_funct_2(D_294,A_292,B_295)
      | ~ v1_funct_1(D_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2417,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_498,c_2409])).

tff(c_2428,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_72,c_58,c_2417])).

tff(c_2430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1388,c_52,c_2428])).

tff(c_2432,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1380])).

tff(c_2435,plain,(
    ! [E_305,B_302,D_304,C_300,A_301,F_303] :
      ( v1_funct_1(k1_partfun1(A_301,B_302,C_300,D_304,E_305,F_303))
      | ~ m1_subset_1(F_303,k1_zfmisc_1(k2_zfmisc_1(C_300,D_304)))
      | ~ v1_funct_1(F_303)
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302)))
      | ~ v1_funct_1(E_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2441,plain,(
    ! [A_301,B_302,E_305] :
      ( v1_funct_1(k1_partfun1(A_301,B_302,'#skF_2','#skF_1',E_305,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302)))
      | ~ v1_funct_1(E_305) ) ),
    inference(resolution,[status(thm)],[c_60,c_2435])).

tff(c_2467,plain,(
    ! [A_310,B_311,E_312] :
      ( v1_funct_1(k1_partfun1(A_310,B_311,'#skF_2','#skF_1',E_312,'#skF_4'))
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311)))
      | ~ v1_funct_1(E_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2441])).

tff(c_2473,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2467])).

tff(c_2480,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_498,c_2473])).

tff(c_2501,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2480,c_529])).

tff(c_2529,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2501])).

tff(c_2530,plain,(
    ! [A_323,C_324,B_325] :
      ( k6_partfun1(A_323) = k5_relat_1(C_324,k2_funct_1(C_324))
      | k1_xboole_0 = B_325
      | ~ v2_funct_1(C_324)
      | k2_relset_1(A_323,B_325,C_324) != B_325
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_323,B_325)))
      | ~ v1_funct_2(C_324,A_323,B_325)
      | ~ v1_funct_1(C_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2534,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2530])).

tff(c_2542,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_2534])).

tff(c_2543,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2542])).

tff(c_2551,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2543,c_8])).

tff(c_2558,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_70,c_54,c_73,c_2551])).

tff(c_2560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2529,c_2558])).

tff(c_2562,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2501])).

tff(c_1373,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_147])).

tff(c_2566,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_1373])).

tff(c_2612,plain,(
    ! [A_329,C_330,B_331] :
      ( k6_partfun1(A_329) = k5_relat_1(C_330,k2_funct_1(C_330))
      | k1_xboole_0 = B_331
      | ~ v2_funct_1(C_330)
      | k2_relset_1(A_329,B_331,C_330) != B_331
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_329,B_331)))
      | ~ v1_funct_2(C_330,A_329,B_331)
      | ~ v1_funct_1(C_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2618,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2612])).

tff(c_2628,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2566,c_2432,c_2618])).

tff(c_2629,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2628])).

tff(c_2647,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2629,c_8])).

tff(c_2654,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_64,c_2432,c_73,c_2647])).

tff(c_2431,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(splitRight,[status(thm)],[c_1380])).

tff(c_2563,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k5_relat_1(B_6,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_2431])).

tff(c_4514,plain,(
    ! [B_423] :
      ( k2_funct_1('#skF_4') = B_423
      | k5_relat_1(B_423,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_423) != '#skF_2'
      | ~ v1_funct_1(B_423)
      | ~ v1_relat_1(B_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_2563])).

tff(c_4610,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_4514])).

tff(c_4701,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_146,c_2516,c_4610])).

tff(c_4705,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4701,c_2629])).

tff(c_4708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1371,c_4705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:13:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.35/2.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.71  
% 7.56/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.72  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.56/2.72  
% 7.56/2.72  %Foreground sorts:
% 7.56/2.72  
% 7.56/2.72  
% 7.56/2.72  %Background operators:
% 7.56/2.72  
% 7.56/2.72  
% 7.56/2.72  %Foreground operators:
% 7.56/2.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.56/2.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.56/2.72  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.56/2.72  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.56/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.56/2.72  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.56/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.56/2.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.56/2.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.56/2.72  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.56/2.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.56/2.72  tff('#skF_2', type, '#skF_2': $i).
% 7.56/2.72  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.56/2.72  tff('#skF_3', type, '#skF_3': $i).
% 7.56/2.72  tff('#skF_1', type, '#skF_1': $i).
% 7.56/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.56/2.72  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.56/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.56/2.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.56/2.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.56/2.72  tff('#skF_4', type, '#skF_4': $i).
% 7.56/2.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.56/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.56/2.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.56/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.56/2.72  
% 7.56/2.74  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.56/2.74  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.56/2.74  tff(f_90, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.56/2.74  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.56/2.74  tff(f_86, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.56/2.74  tff(f_102, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.56/2.74  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.56/2.74  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.56/2.74  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.56/2.74  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 7.56/2.74  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.56/2.74  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 7.56/2.74  tff(f_119, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.56/2.74  tff(f_31, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 7.56/2.74  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.56/2.74  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_276, plain, (![C_85, E_87, F_88, A_89, B_86, D_90]: (k1_partfun1(A_89, B_86, C_85, D_90, E_87, F_88)=k5_relat_1(E_87, F_88) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_85, D_90))) | ~v1_funct_1(F_88) | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_86))) | ~v1_funct_1(E_87))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.56/2.74  tff(c_282, plain, (![A_89, B_86, E_87]: (k1_partfun1(A_89, B_86, '#skF_2', '#skF_1', E_87, '#skF_4')=k5_relat_1(E_87, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_86))) | ~v1_funct_1(E_87))), inference(resolution, [status(thm)], [c_60, c_276])).
% 7.56/2.74  tff(c_365, plain, (![A_103, B_104, E_105]: (k1_partfun1(A_103, B_104, '#skF_2', '#skF_1', E_105, '#skF_4')=k5_relat_1(E_105, '#skF_4') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(E_105))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_282])).
% 7.56/2.74  tff(c_371, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_365])).
% 7.56/2.74  tff(c_378, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_371])).
% 7.56/2.74  tff(c_28, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.56/2.74  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_184, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r2_relset_1(A_68, B_69, C_67, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.56/2.74  tff(c_192, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_184])).
% 7.56/2.74  tff(c_207, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_192])).
% 7.56/2.74  tff(c_208, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_207])).
% 7.56/2.74  tff(c_383, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_208])).
% 7.56/2.74  tff(c_440, plain, (![B_111, A_110, F_112, C_109, D_113, E_114]: (m1_subset_1(k1_partfun1(A_110, B_111, C_109, D_113, E_114, F_112), k1_zfmisc_1(k2_zfmisc_1(A_110, D_113))) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_109, D_113))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.56/2.74  tff(c_474, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_378, c_440])).
% 7.56/2.74  tff(c_495, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_474])).
% 7.56/2.74  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_383, c_495])).
% 7.56/2.74  tff(c_498, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_207])).
% 7.56/2.74  tff(c_541, plain, (![B_121, D_123, A_120, C_119, E_124, F_122]: (v1_funct_1(k1_partfun1(A_120, B_121, C_119, D_123, E_124, F_122)) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_119, D_123))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.56/2.74  tff(c_547, plain, (![A_120, B_121, E_124]: (v1_funct_1(k1_partfun1(A_120, B_121, '#skF_2', '#skF_1', E_124, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(E_124))), inference(resolution, [status(thm)], [c_60, c_541])).
% 7.56/2.74  tff(c_572, plain, (![A_128, B_129, E_130]: (v1_funct_1(k1_partfun1(A_128, B_129, '#skF_2', '#skF_1', E_130, '#skF_4')) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_547])).
% 7.56/2.74  tff(c_578, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_572])).
% 7.56/2.74  tff(c_585, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_498, c_578])).
% 7.56/2.74  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.56/2.74  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.56/2.74  tff(c_73, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4])).
% 7.56/2.74  tff(c_109, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.56/2.74  tff(c_119, plain, (![A_23]: (v1_relat_1(k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_28, c_109])).
% 7.56/2.74  tff(c_120, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_109])).
% 7.56/2.74  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_133, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.56/2.74  tff(c_139, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_133])).
% 7.56/2.74  tff(c_146, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_139])).
% 7.56/2.74  tff(c_12, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.56/2.74  tff(c_507, plain, (![A_115, B_116]: (k2_funct_1(A_115)=B_116 | k6_partfun1(k2_relat_1(A_115))!=k5_relat_1(B_116, A_115) | k2_relat_1(B_116)!=k1_relat_1(A_115) | ~v2_funct_1(A_115) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 7.56/2.74  tff(c_511, plain, (![B_116]: (k2_funct_1('#skF_3')=B_116 | k5_relat_1(B_116, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_116)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_507])).
% 7.56/2.74  tff(c_518, plain, (![B_117]: (k2_funct_1('#skF_3')=B_117 | k5_relat_1(B_117, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_117)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_70, c_54, c_511])).
% 7.56/2.74  tff(c_521, plain, (![A_23]: (k6_partfun1(A_23)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_23), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_23))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_119, c_518])).
% 7.56/2.74  tff(c_529, plain, (![A_23]: (k6_partfun1(A_23)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_23), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_23 | ~v1_funct_1(k6_partfun1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_521])).
% 7.56/2.74  tff(c_592, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_585, c_529])).
% 7.56/2.74  tff(c_595, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_592])).
% 7.56/2.74  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_650, plain, (![A_143, C_144, B_145]: (k6_partfun1(A_143)=k5_relat_1(C_144, k2_funct_1(C_144)) | k1_xboole_0=B_145 | ~v2_funct_1(C_144) | k2_relset_1(A_143, B_145, C_144)!=B_145 | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_143, B_145))) | ~v1_funct_2(C_144, A_143, B_145) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.56/2.74  tff(c_654, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_650])).
% 7.56/2.74  tff(c_662, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_654])).
% 7.56/2.74  tff(c_663, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_662])).
% 7.56/2.74  tff(c_8, plain, (![A_3]: (k2_relat_1(k5_relat_1(A_3, k2_funct_1(A_3)))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.56/2.74  tff(c_671, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_663, c_8])).
% 7.56/2.74  tff(c_678, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_70, c_54, c_73, c_671])).
% 7.56/2.74  tff(c_680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_678])).
% 7.56/2.74  tff(c_682, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_592])).
% 7.56/2.74  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_121, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_109])).
% 7.56/2.74  tff(c_524, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_121, c_518])).
% 7.56/2.74  tff(c_532, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_524])).
% 7.56/2.74  tff(c_533, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_532])).
% 7.56/2.74  tff(c_537, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_533])).
% 7.56/2.74  tff(c_685, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_682, c_537])).
% 7.56/2.74  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_123, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.56/2.74  tff(c_130, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_28, c_123])).
% 7.56/2.74  tff(c_147, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_133])).
% 7.56/2.74  tff(c_1358, plain, (![A_196, B_197, C_198, D_199]: (k2_relset_1(A_196, B_197, C_198)=B_197 | ~r2_relset_1(B_197, B_197, k1_partfun1(B_197, A_196, A_196, B_197, D_199, C_198), k6_partfun1(B_197)) | ~m1_subset_1(D_199, k1_zfmisc_1(k2_zfmisc_1(B_197, A_196))) | ~v1_funct_2(D_199, B_197, A_196) | ~v1_funct_1(D_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_2(C_198, A_196, B_197) | ~v1_funct_1(C_198))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.56/2.74  tff(c_1364, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_498, c_1358])).
% 7.56/2.74  tff(c_1368, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_130, c_147, c_1364])).
% 7.56/2.74  tff(c_1370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_1368])).
% 7.56/2.74  tff(c_1371, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_533])).
% 7.56/2.74  tff(c_2484, plain, (![A_317, F_316, C_313, B_314, E_315, D_318]: (k1_partfun1(A_317, B_314, C_313, D_318, E_315, F_316)=k5_relat_1(E_315, F_316) | ~m1_subset_1(F_316, k1_zfmisc_1(k2_zfmisc_1(C_313, D_318))) | ~v1_funct_1(F_316) | ~m1_subset_1(E_315, k1_zfmisc_1(k2_zfmisc_1(A_317, B_314))) | ~v1_funct_1(E_315))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.56/2.74  tff(c_2490, plain, (![A_317, B_314, E_315]: (k1_partfun1(A_317, B_314, '#skF_2', '#skF_1', E_315, '#skF_4')=k5_relat_1(E_315, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_315, k1_zfmisc_1(k2_zfmisc_1(A_317, B_314))) | ~v1_funct_1(E_315))), inference(resolution, [status(thm)], [c_60, c_2484])).
% 7.56/2.74  tff(c_2503, plain, (![A_320, B_321, E_322]: (k1_partfun1(A_320, B_321, '#skF_2', '#skF_1', E_322, '#skF_4')=k5_relat_1(E_322, '#skF_4') | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))) | ~v1_funct_1(E_322))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2490])).
% 7.56/2.74  tff(c_2509, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2503])).
% 7.56/2.74  tff(c_2516, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_498, c_2509])).
% 7.56/2.74  tff(c_1372, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_533])).
% 7.56/2.74  tff(c_71, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_partfun1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 7.56/2.74  tff(c_1376, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1372, c_71])).
% 7.56/2.74  tff(c_1380, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_64, c_1376])).
% 7.56/2.74  tff(c_1388, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1380])).
% 7.56/2.74  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.56/2.74  tff(c_6, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.56/2.74  tff(c_72, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 7.56/2.74  tff(c_2409, plain, (![C_296, D_294, E_293, A_292, B_295]: (k1_xboole_0=C_296 | v2_funct_1(E_293) | k2_relset_1(A_292, B_295, D_294)!=B_295 | ~v2_funct_1(k1_partfun1(A_292, B_295, B_295, C_296, D_294, E_293)) | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(B_295, C_296))) | ~v1_funct_2(E_293, B_295, C_296) | ~v1_funct_1(E_293) | ~m1_subset_1(D_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_295))) | ~v1_funct_2(D_294, A_292, B_295) | ~v1_funct_1(D_294))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.56/2.74  tff(c_2417, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_498, c_2409])).
% 7.56/2.74  tff(c_2428, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_72, c_58, c_2417])).
% 7.56/2.74  tff(c_2430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1388, c_52, c_2428])).
% 7.56/2.74  tff(c_2432, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1380])).
% 7.56/2.74  tff(c_2435, plain, (![E_305, B_302, D_304, C_300, A_301, F_303]: (v1_funct_1(k1_partfun1(A_301, B_302, C_300, D_304, E_305, F_303)) | ~m1_subset_1(F_303, k1_zfmisc_1(k2_zfmisc_1(C_300, D_304))) | ~v1_funct_1(F_303) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))) | ~v1_funct_1(E_305))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.56/2.74  tff(c_2441, plain, (![A_301, B_302, E_305]: (v1_funct_1(k1_partfun1(A_301, B_302, '#skF_2', '#skF_1', E_305, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))) | ~v1_funct_1(E_305))), inference(resolution, [status(thm)], [c_60, c_2435])).
% 7.56/2.74  tff(c_2467, plain, (![A_310, B_311, E_312]: (v1_funct_1(k1_partfun1(A_310, B_311, '#skF_2', '#skF_1', E_312, '#skF_4')) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))) | ~v1_funct_1(E_312))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2441])).
% 7.56/2.74  tff(c_2473, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2467])).
% 7.56/2.74  tff(c_2480, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_498, c_2473])).
% 7.56/2.74  tff(c_2501, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2480, c_529])).
% 7.56/2.74  tff(c_2529, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2501])).
% 7.56/2.74  tff(c_2530, plain, (![A_323, C_324, B_325]: (k6_partfun1(A_323)=k5_relat_1(C_324, k2_funct_1(C_324)) | k1_xboole_0=B_325 | ~v2_funct_1(C_324) | k2_relset_1(A_323, B_325, C_324)!=B_325 | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_323, B_325))) | ~v1_funct_2(C_324, A_323, B_325) | ~v1_funct_1(C_324))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.56/2.74  tff(c_2534, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2530])).
% 7.56/2.74  tff(c_2542, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_2534])).
% 7.56/2.74  tff(c_2543, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_2542])).
% 7.56/2.74  tff(c_2551, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2543, c_8])).
% 7.56/2.74  tff(c_2558, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_70, c_54, c_73, c_2551])).
% 7.56/2.74  tff(c_2560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2529, c_2558])).
% 7.56/2.74  tff(c_2562, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2501])).
% 7.56/2.74  tff(c_1373, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_147])).
% 7.56/2.74  tff(c_2566, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_1373])).
% 7.56/2.74  tff(c_2612, plain, (![A_329, C_330, B_331]: (k6_partfun1(A_329)=k5_relat_1(C_330, k2_funct_1(C_330)) | k1_xboole_0=B_331 | ~v2_funct_1(C_330) | k2_relset_1(A_329, B_331, C_330)!=B_331 | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_329, B_331))) | ~v1_funct_2(C_330, A_329, B_331) | ~v1_funct_1(C_330))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.56/2.74  tff(c_2618, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2612])).
% 7.56/2.74  tff(c_2628, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2566, c_2432, c_2618])).
% 7.56/2.74  tff(c_2629, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_2628])).
% 7.56/2.74  tff(c_2647, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2629, c_8])).
% 7.56/2.74  tff(c_2654, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_64, c_2432, c_73, c_2647])).
% 7.56/2.74  tff(c_2431, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(splitRight, [status(thm)], [c_1380])).
% 7.56/2.74  tff(c_2563, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k5_relat_1(B_6, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_2431])).
% 7.56/2.74  tff(c_4514, plain, (![B_423]: (k2_funct_1('#skF_4')=B_423 | k5_relat_1(B_423, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_423)!='#skF_2' | ~v1_funct_1(B_423) | ~v1_relat_1(B_423))), inference(demodulation, [status(thm), theory('equality')], [c_2654, c_2563])).
% 7.56/2.74  tff(c_4610, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_4514])).
% 7.56/2.74  tff(c_4701, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_146, c_2516, c_4610])).
% 7.56/2.74  tff(c_4705, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4701, c_2629])).
% 7.56/2.74  tff(c_4708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1371, c_4705])).
% 7.56/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.74  
% 7.56/2.74  Inference rules
% 7.56/2.74  ----------------------
% 7.56/2.74  #Ref     : 0
% 7.56/2.74  #Sup     : 964
% 7.56/2.74  #Fact    : 0
% 7.56/2.74  #Define  : 0
% 7.56/2.74  #Split   : 28
% 7.56/2.74  #Chain   : 0
% 7.56/2.74  #Close   : 0
% 7.56/2.74  
% 7.56/2.74  Ordering : KBO
% 7.56/2.74  
% 7.56/2.74  Simplification rules
% 7.56/2.74  ----------------------
% 7.56/2.74  #Subsume      : 40
% 7.56/2.74  #Demod        : 1282
% 7.56/2.74  #Tautology    : 269
% 7.56/2.74  #SimpNegUnit  : 100
% 7.56/2.74  #BackRed      : 49
% 7.56/2.74  
% 7.56/2.74  #Partial instantiations: 0
% 7.56/2.74  #Strategies tried      : 1
% 7.56/2.74  
% 7.56/2.75  Timing (in seconds)
% 7.56/2.75  ----------------------
% 7.56/2.75  Preprocessing        : 0.49
% 7.56/2.75  Parsing              : 0.26
% 7.56/2.75  CNF conversion       : 0.03
% 7.56/2.75  Main loop            : 1.37
% 7.56/2.75  Inferencing          : 0.46
% 7.56/2.75  Reduction            : 0.54
% 7.56/2.75  Demodulation         : 0.41
% 7.56/2.75  BG Simplification    : 0.05
% 7.56/2.75  Subsumption          : 0.24
% 7.56/2.75  Abstraction          : 0.06
% 7.56/2.75  MUC search           : 0.00
% 7.56/2.75  Cooper               : 0.00
% 7.56/2.75  Total                : 1.92
% 7.56/2.75  Index Insertion      : 0.00
% 7.56/2.75  Index Deletion       : 0.00
% 7.56/2.75  Index Matching       : 0.00
% 7.56/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
