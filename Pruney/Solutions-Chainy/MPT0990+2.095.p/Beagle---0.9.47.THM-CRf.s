%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:10 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 8.12s
% Verified   : 
% Statistics : Number of formulae       :  168 (1124 expanded)
%              Number of leaves         :   40 ( 410 expanded)
%              Depth                    :   23
%              Number of atoms          :  425 (4732 expanded)
%              Number of equality atoms :  165 (1686 expanded)
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
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

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

tff(c_288,plain,(
    ! [C_85,E_87,F_88,A_89,B_86,D_90] :
      ( k1_partfun1(A_89,B_86,C_85,D_90,E_87,F_88) = k5_relat_1(E_87,F_88)
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_85,D_90)))
      | ~ v1_funct_1(F_88)
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_294,plain,(
    ! [A_89,B_86,E_87] :
      ( k1_partfun1(A_89,B_86,'#skF_2','#skF_1',E_87,'#skF_4') = k5_relat_1(E_87,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(resolution,[status(thm)],[c_60,c_288])).

tff(c_387,plain,(
    ! [A_103,B_104,E_105] :
      ( k1_partfun1(A_103,B_104,'#skF_2','#skF_1',E_105,'#skF_4') = k5_relat_1(E_105,'#skF_4')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_294])).

tff(c_393,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_387])).

tff(c_400,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_393])).

tff(c_28,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_167,plain,(
    ! [D_63,C_64,A_65,B_66] :
      ( D_63 = C_64
      | ~ r2_relset_1(A_65,B_66,C_64,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_173,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_167])).

tff(c_184,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_173])).

tff(c_210,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_405,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_210])).

tff(c_514,plain,(
    ! [B_111,A_110,F_112,C_109,D_113,E_114] :
      ( m1_subset_1(k1_partfun1(A_110,B_111,C_109,D_113,E_114,F_112),k1_zfmisc_1(k2_zfmisc_1(A_110,D_113)))
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_109,D_113)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_545,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_514])).

tff(c_564,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_545])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_564])).

tff(c_570,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_615,plain,(
    ! [D_122,A_119,F_121,B_120,E_123,C_118] :
      ( v1_funct_1(k1_partfun1(A_119,B_120,C_118,D_122,E_123,F_121))
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_118,D_122)))
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_621,plain,(
    ! [A_119,B_120,E_123] :
      ( v1_funct_1(k1_partfun1(A_119,B_120,'#skF_2','#skF_1',E_123,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_123) ) ),
    inference(resolution,[status(thm)],[c_60,c_615])).

tff(c_629,plain,(
    ! [A_124,B_125,E_126] :
      ( v1_funct_1(k1_partfun1(A_124,B_125,'#skF_2','#skF_1',E_126,'#skF_4'))
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_1(E_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_621])).

tff(c_635,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_629])).

tff(c_642,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_570,c_635])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4])).

tff(c_111,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_121,plain,(
    ! [A_23] : v1_relat_1(k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_28,c_111])).

tff(c_122,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_111])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_135,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_141,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_135])).

tff(c_148,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_141])).

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

tff(c_579,plain,(
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

tff(c_585,plain,(
    ! [B_116] :
      ( k2_funct_1('#skF_3') = B_116
      | k5_relat_1(B_116,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_116) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_579])).

tff(c_594,plain,(
    ! [B_117] :
      ( k2_funct_1('#skF_3') = B_117
      | k5_relat_1(B_117,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_117) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_70,c_54,c_585])).

tff(c_597,plain,(
    ! [A_23] :
      ( k6_partfun1(A_23) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_23),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_23)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_121,c_594])).

tff(c_680,plain,(
    ! [A_138] :
      ( k6_partfun1(A_138) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_138),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_138
      | ~ v1_funct_1(k6_partfun1(A_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_597])).

tff(c_684,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_642,c_680])).

tff(c_685,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_717,plain,(
    ! [A_143,C_144,B_145] :
      ( k6_partfun1(A_143) = k5_relat_1(C_144,k2_funct_1(C_144))
      | k1_xboole_0 = B_145
      | ~ v2_funct_1(C_144)
      | k2_relset_1(A_143,B_145,C_144) != B_145
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_143,B_145)))
      | ~ v1_funct_2(C_144,A_143,B_145)
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_721,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_717])).

tff(c_729,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_721])).

tff(c_730,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_729])).

tff(c_10,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10])).

tff(c_738,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_72])).

tff(c_745,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_70,c_54,c_738])).

tff(c_777,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_75])).

tff(c_800,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_777])).

tff(c_802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_800])).

tff(c_804,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_123,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_111])).

tff(c_600,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_123,c_594])).

tff(c_608,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_600])).

tff(c_609,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_608])).

tff(c_613,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_609])).

tff(c_807,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_613])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_125,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_149,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_135])).

tff(c_1535,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k2_relset_1(A_186,B_187,C_188) = B_187
      | ~ r2_relset_1(B_187,B_187,k1_partfun1(B_187,A_186,A_186,B_187,D_189,C_188),k6_partfun1(B_187))
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(B_187,A_186)))
      | ~ v1_funct_2(D_189,B_187,A_186)
      | ~ v1_funct_1(D_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_2(C_188,A_186,B_187)
      | ~ v1_funct_1(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1541,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_1535])).

tff(c_1545,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_132,c_149,c_1541])).

tff(c_1547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_807,c_1545])).

tff(c_1548,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_609])).

tff(c_2623,plain,(
    ! [B_289,C_288,E_290,F_291,D_293,A_292] :
      ( k1_partfun1(A_292,B_289,C_288,D_293,E_290,F_291) = k5_relat_1(E_290,F_291)
      | ~ m1_subset_1(F_291,k1_zfmisc_1(k2_zfmisc_1(C_288,D_293)))
      | ~ v1_funct_1(F_291)
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(A_292,B_289)))
      | ~ v1_funct_1(E_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2629,plain,(
    ! [A_292,B_289,E_290] :
      ( k1_partfun1(A_292,B_289,'#skF_2','#skF_1',E_290,'#skF_4') = k5_relat_1(E_290,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(A_292,B_289)))
      | ~ v1_funct_1(E_290) ) ),
    inference(resolution,[status(thm)],[c_60,c_2623])).

tff(c_2642,plain,(
    ! [A_295,B_296,E_297] :
      ( k1_partfun1(A_295,B_296,'#skF_2','#skF_1',E_297,'#skF_4') = k5_relat_1(E_297,'#skF_4')
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296)))
      | ~ v1_funct_1(E_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2629])).

tff(c_2648,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2642])).

tff(c_2655,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_570,c_2648])).

tff(c_1549,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_609])).

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

tff(c_1553,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1549,c_71])).

tff(c_1557,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_64,c_1553])).

tff(c_1565,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1557])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_6,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_2536,plain,(
    ! [B_270,A_267,C_271,D_269,E_268] :
      ( k1_xboole_0 = C_271
      | v2_funct_1(E_268)
      | k2_relset_1(A_267,B_270,D_269) != B_270
      | ~ v2_funct_1(k1_partfun1(A_267,B_270,B_270,C_271,D_269,E_268))
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(B_270,C_271)))
      | ~ v1_funct_2(E_268,B_270,C_271)
      | ~ v1_funct_1(E_268)
      | ~ m1_subset_1(D_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_270)))
      | ~ v1_funct_2(D_269,A_267,B_270)
      | ~ v1_funct_1(D_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2544,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_570,c_2536])).

tff(c_2555,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_74,c_58,c_2544])).

tff(c_2557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1565,c_52,c_2555])).

tff(c_2559,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1557])).

tff(c_2574,plain,(
    ! [C_275,A_276,B_277,E_280,D_279,F_278] :
      ( v1_funct_1(k1_partfun1(A_276,B_277,C_275,D_279,E_280,F_278))
      | ~ m1_subset_1(F_278,k1_zfmisc_1(k2_zfmisc_1(C_275,D_279)))
      | ~ v1_funct_1(F_278)
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ v1_funct_1(E_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2580,plain,(
    ! [A_276,B_277,E_280] :
      ( v1_funct_1(k1_partfun1(A_276,B_277,'#skF_2','#skF_1',E_280,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ v1_funct_1(E_280) ) ),
    inference(resolution,[status(thm)],[c_60,c_2574])).

tff(c_2606,plain,(
    ! [A_285,B_286,E_287] :
      ( v1_funct_1(k1_partfun1(A_285,B_286,'#skF_2','#skF_1',E_287,'#skF_4'))
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2580])).

tff(c_2612,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2606])).

tff(c_2619,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_570,c_2612])).

tff(c_605,plain,(
    ! [A_23] :
      ( k6_partfun1(A_23) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_23),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_23
      | ~ v1_funct_1(k6_partfun1(A_23)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_597])).

tff(c_2640,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2619,c_605])).

tff(c_2668,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2640])).

tff(c_2669,plain,(
    ! [A_298,C_299,B_300] :
      ( k6_partfun1(A_298) = k5_relat_1(C_299,k2_funct_1(C_299))
      | k1_xboole_0 = B_300
      | ~ v2_funct_1(C_299)
      | k2_relset_1(A_298,B_300,C_299) != B_300
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_298,B_300)))
      | ~ v1_funct_2(C_299,A_298,B_300)
      | ~ v1_funct_1(C_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2673,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2669])).

tff(c_2681,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_2673])).

tff(c_2682,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2681])).

tff(c_2690,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2682,c_72])).

tff(c_2697,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_70,c_54,c_2690])).

tff(c_2730,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2697,c_75])).

tff(c_2753,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_2730])).

tff(c_2755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2668,c_2753])).

tff(c_2757,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2640])).

tff(c_1550,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_149])).

tff(c_2761,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2757,c_1550])).

tff(c_2802,plain,(
    ! [A_304,C_305,B_306] :
      ( k6_partfun1(A_304) = k5_relat_1(C_305,k2_funct_1(C_305))
      | k1_xboole_0 = B_306
      | ~ v2_funct_1(C_305)
      | k2_relset_1(A_304,B_306,C_305) != B_306
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_304,B_306)))
      | ~ v1_funct_2(C_305,A_304,B_306)
      | ~ v1_funct_1(C_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2808,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2802])).

tff(c_2818,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2761,c_2559,c_2808])).

tff(c_2819,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2818])).

tff(c_2837,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2819,c_72])).

tff(c_2844,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_64,c_2559,c_2837])).

tff(c_2873,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2844,c_75])).

tff(c_2890,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_2873])).

tff(c_2558,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(splitRight,[status(thm)],[c_1557])).

tff(c_2758,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k5_relat_1(B_6,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2757,c_2558])).

tff(c_5124,plain,(
    ! [B_412] :
      ( k2_funct_1('#skF_4') = B_412
      | k5_relat_1(B_412,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_412) != '#skF_2'
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2890,c_2758])).

tff(c_5220,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_5124])).

tff(c_5311,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_148,c_2655,c_5220])).

tff(c_5314,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5311,c_2819])).

tff(c_5317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1548,c_5314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:50:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.69  
% 8.01/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.69  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.01/2.69  
% 8.01/2.69  %Foreground sorts:
% 8.01/2.69  
% 8.01/2.69  
% 8.01/2.69  %Background operators:
% 8.01/2.69  
% 8.01/2.69  
% 8.01/2.69  %Foreground operators:
% 8.01/2.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.01/2.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.01/2.69  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.01/2.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.01/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.01/2.69  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.01/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.01/2.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.01/2.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.01/2.69  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.01/2.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.01/2.69  tff('#skF_2', type, '#skF_2': $i).
% 8.01/2.69  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.01/2.69  tff('#skF_3', type, '#skF_3': $i).
% 8.01/2.69  tff('#skF_1', type, '#skF_1': $i).
% 8.01/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.01/2.69  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.01/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.01/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.01/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.01/2.69  tff('#skF_4', type, '#skF_4': $i).
% 8.01/2.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.01/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.01/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.01/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.01/2.69  
% 8.12/2.72  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 8.12/2.72  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.12/2.72  tff(f_90, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.12/2.72  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.12/2.72  tff(f_86, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.12/2.72  tff(f_102, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.12/2.72  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.12/2.72  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.12/2.72  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.12/2.72  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 8.12/2.72  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 8.12/2.72  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 8.12/2.72  tff(f_119, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 8.12/2.72  tff(f_31, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 8.12/2.72  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 8.12/2.72  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_288, plain, (![C_85, E_87, F_88, A_89, B_86, D_90]: (k1_partfun1(A_89, B_86, C_85, D_90, E_87, F_88)=k5_relat_1(E_87, F_88) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_85, D_90))) | ~v1_funct_1(F_88) | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_86))) | ~v1_funct_1(E_87))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.12/2.72  tff(c_294, plain, (![A_89, B_86, E_87]: (k1_partfun1(A_89, B_86, '#skF_2', '#skF_1', E_87, '#skF_4')=k5_relat_1(E_87, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_86))) | ~v1_funct_1(E_87))), inference(resolution, [status(thm)], [c_60, c_288])).
% 8.12/2.72  tff(c_387, plain, (![A_103, B_104, E_105]: (k1_partfun1(A_103, B_104, '#skF_2', '#skF_1', E_105, '#skF_4')=k5_relat_1(E_105, '#skF_4') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(E_105))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_294])).
% 8.12/2.72  tff(c_393, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_387])).
% 8.12/2.72  tff(c_400, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_393])).
% 8.12/2.72  tff(c_28, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.12/2.72  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_167, plain, (![D_63, C_64, A_65, B_66]: (D_63=C_64 | ~r2_relset_1(A_65, B_66, C_64, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.12/2.72  tff(c_173, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_167])).
% 8.12/2.72  tff(c_184, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_173])).
% 8.12/2.72  tff(c_210, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_184])).
% 8.12/2.72  tff(c_405, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_210])).
% 8.12/2.72  tff(c_514, plain, (![B_111, A_110, F_112, C_109, D_113, E_114]: (m1_subset_1(k1_partfun1(A_110, B_111, C_109, D_113, E_114, F_112), k1_zfmisc_1(k2_zfmisc_1(A_110, D_113))) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_109, D_113))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.12/2.72  tff(c_545, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_400, c_514])).
% 8.12/2.72  tff(c_564, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_545])).
% 8.12/2.72  tff(c_569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_405, c_564])).
% 8.12/2.72  tff(c_570, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_184])).
% 8.12/2.72  tff(c_615, plain, (![D_122, A_119, F_121, B_120, E_123, C_118]: (v1_funct_1(k1_partfun1(A_119, B_120, C_118, D_122, E_123, F_121)) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_118, D_122))) | ~v1_funct_1(F_121) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_123))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.12/2.72  tff(c_621, plain, (![A_119, B_120, E_123]: (v1_funct_1(k1_partfun1(A_119, B_120, '#skF_2', '#skF_1', E_123, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_123))), inference(resolution, [status(thm)], [c_60, c_615])).
% 8.12/2.72  tff(c_629, plain, (![A_124, B_125, E_126]: (v1_funct_1(k1_partfun1(A_124, B_125, '#skF_2', '#skF_1', E_126, '#skF_4')) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_1(E_126))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_621])).
% 8.12/2.72  tff(c_635, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_629])).
% 8.12/2.72  tff(c_642, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_570, c_635])).
% 8.12/2.72  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.12/2.72  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.12/2.72  tff(c_75, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4])).
% 8.12/2.72  tff(c_111, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.12/2.72  tff(c_121, plain, (![A_23]: (v1_relat_1(k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_28, c_111])).
% 8.12/2.72  tff(c_122, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_111])).
% 8.12/2.72  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_135, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.12/2.72  tff(c_141, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_135])).
% 8.12/2.72  tff(c_148, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_141])).
% 8.12/2.72  tff(c_12, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.12/2.72  tff(c_579, plain, (![A_115, B_116]: (k2_funct_1(A_115)=B_116 | k6_partfun1(k2_relat_1(A_115))!=k5_relat_1(B_116, A_115) | k2_relat_1(B_116)!=k1_relat_1(A_115) | ~v2_funct_1(A_115) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 8.12/2.72  tff(c_585, plain, (![B_116]: (k2_funct_1('#skF_3')=B_116 | k5_relat_1(B_116, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_116)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_579])).
% 8.12/2.72  tff(c_594, plain, (![B_117]: (k2_funct_1('#skF_3')=B_117 | k5_relat_1(B_117, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_117)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_70, c_54, c_585])).
% 8.12/2.72  tff(c_597, plain, (![A_23]: (k6_partfun1(A_23)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_23), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_23))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_121, c_594])).
% 8.12/2.72  tff(c_680, plain, (![A_138]: (k6_partfun1(A_138)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_138), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_138 | ~v1_funct_1(k6_partfun1(A_138)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_597])).
% 8.12/2.72  tff(c_684, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_642, c_680])).
% 8.12/2.72  tff(c_685, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_684])).
% 8.12/2.72  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_717, plain, (![A_143, C_144, B_145]: (k6_partfun1(A_143)=k5_relat_1(C_144, k2_funct_1(C_144)) | k1_xboole_0=B_145 | ~v2_funct_1(C_144) | k2_relset_1(A_143, B_145, C_144)!=B_145 | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_143, B_145))) | ~v1_funct_2(C_144, A_143, B_145) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.12/2.72  tff(c_721, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_717])).
% 8.12/2.72  tff(c_729, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_721])).
% 8.12/2.72  tff(c_730, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_729])).
% 8.12/2.72  tff(c_10, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.12/2.72  tff(c_72, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10])).
% 8.12/2.72  tff(c_738, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_730, c_72])).
% 8.12/2.72  tff(c_745, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_70, c_54, c_738])).
% 8.12/2.72  tff(c_777, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_745, c_75])).
% 8.12/2.72  tff(c_800, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_777])).
% 8.12/2.72  tff(c_802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_800])).
% 8.12/2.72  tff(c_804, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_684])).
% 8.12/2.72  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_123, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_111])).
% 8.12/2.72  tff(c_600, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_123, c_594])).
% 8.12/2.72  tff(c_608, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_600])).
% 8.12/2.72  tff(c_609, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_608])).
% 8.12/2.72  tff(c_613, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_609])).
% 8.12/2.72  tff(c_807, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_804, c_613])).
% 8.12/2.72  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_125, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.12/2.72  tff(c_132, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_28, c_125])).
% 8.12/2.72  tff(c_149, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_135])).
% 8.12/2.72  tff(c_1535, plain, (![A_186, B_187, C_188, D_189]: (k2_relset_1(A_186, B_187, C_188)=B_187 | ~r2_relset_1(B_187, B_187, k1_partfun1(B_187, A_186, A_186, B_187, D_189, C_188), k6_partfun1(B_187)) | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(B_187, A_186))) | ~v1_funct_2(D_189, B_187, A_186) | ~v1_funct_1(D_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_2(C_188, A_186, B_187) | ~v1_funct_1(C_188))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.12/2.72  tff(c_1541, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_570, c_1535])).
% 8.12/2.72  tff(c_1545, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_132, c_149, c_1541])).
% 8.12/2.72  tff(c_1547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_807, c_1545])).
% 8.12/2.72  tff(c_1548, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_609])).
% 8.12/2.72  tff(c_2623, plain, (![B_289, C_288, E_290, F_291, D_293, A_292]: (k1_partfun1(A_292, B_289, C_288, D_293, E_290, F_291)=k5_relat_1(E_290, F_291) | ~m1_subset_1(F_291, k1_zfmisc_1(k2_zfmisc_1(C_288, D_293))) | ~v1_funct_1(F_291) | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(A_292, B_289))) | ~v1_funct_1(E_290))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.12/2.72  tff(c_2629, plain, (![A_292, B_289, E_290]: (k1_partfun1(A_292, B_289, '#skF_2', '#skF_1', E_290, '#skF_4')=k5_relat_1(E_290, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(A_292, B_289))) | ~v1_funct_1(E_290))), inference(resolution, [status(thm)], [c_60, c_2623])).
% 8.12/2.72  tff(c_2642, plain, (![A_295, B_296, E_297]: (k1_partfun1(A_295, B_296, '#skF_2', '#skF_1', E_297, '#skF_4')=k5_relat_1(E_297, '#skF_4') | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))) | ~v1_funct_1(E_297))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2629])).
% 8.12/2.72  tff(c_2648, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2642])).
% 8.12/2.72  tff(c_2655, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_570, c_2648])).
% 8.12/2.72  tff(c_1549, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_609])).
% 8.12/2.72  tff(c_71, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_partfun1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 8.12/2.72  tff(c_1553, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1549, c_71])).
% 8.12/2.72  tff(c_1557, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_64, c_1553])).
% 8.12/2.72  tff(c_1565, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1557])).
% 8.12/2.72  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_187])).
% 8.12/2.72  tff(c_6, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.12/2.72  tff(c_74, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 8.12/2.72  tff(c_2536, plain, (![B_270, A_267, C_271, D_269, E_268]: (k1_xboole_0=C_271 | v2_funct_1(E_268) | k2_relset_1(A_267, B_270, D_269)!=B_270 | ~v2_funct_1(k1_partfun1(A_267, B_270, B_270, C_271, D_269, E_268)) | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(B_270, C_271))) | ~v1_funct_2(E_268, B_270, C_271) | ~v1_funct_1(E_268) | ~m1_subset_1(D_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_270))) | ~v1_funct_2(D_269, A_267, B_270) | ~v1_funct_1(D_269))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.12/2.72  tff(c_2544, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_2536])).
% 8.12/2.72  tff(c_2555, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_74, c_58, c_2544])).
% 8.12/2.72  tff(c_2557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1565, c_52, c_2555])).
% 8.12/2.72  tff(c_2559, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1557])).
% 8.12/2.72  tff(c_2574, plain, (![C_275, A_276, B_277, E_280, D_279, F_278]: (v1_funct_1(k1_partfun1(A_276, B_277, C_275, D_279, E_280, F_278)) | ~m1_subset_1(F_278, k1_zfmisc_1(k2_zfmisc_1(C_275, D_279))) | ~v1_funct_1(F_278) | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~v1_funct_1(E_280))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.12/2.72  tff(c_2580, plain, (![A_276, B_277, E_280]: (v1_funct_1(k1_partfun1(A_276, B_277, '#skF_2', '#skF_1', E_280, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~v1_funct_1(E_280))), inference(resolution, [status(thm)], [c_60, c_2574])).
% 8.12/2.72  tff(c_2606, plain, (![A_285, B_286, E_287]: (v1_funct_1(k1_partfun1(A_285, B_286, '#skF_2', '#skF_1', E_287, '#skF_4')) | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_287))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2580])).
% 8.12/2.72  tff(c_2612, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2606])).
% 8.12/2.72  tff(c_2619, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_570, c_2612])).
% 8.12/2.72  tff(c_605, plain, (![A_23]: (k6_partfun1(A_23)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_23), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_23 | ~v1_funct_1(k6_partfun1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_597])).
% 8.12/2.72  tff(c_2640, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2619, c_605])).
% 8.12/2.72  tff(c_2668, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2640])).
% 8.12/2.72  tff(c_2669, plain, (![A_298, C_299, B_300]: (k6_partfun1(A_298)=k5_relat_1(C_299, k2_funct_1(C_299)) | k1_xboole_0=B_300 | ~v2_funct_1(C_299) | k2_relset_1(A_298, B_300, C_299)!=B_300 | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_298, B_300))) | ~v1_funct_2(C_299, A_298, B_300) | ~v1_funct_1(C_299))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.12/2.72  tff(c_2673, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2669])).
% 8.12/2.72  tff(c_2681, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_2673])).
% 8.12/2.72  tff(c_2682, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_2681])).
% 8.12/2.72  tff(c_2690, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2682, c_72])).
% 8.12/2.72  tff(c_2697, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_70, c_54, c_2690])).
% 8.12/2.72  tff(c_2730, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2697, c_75])).
% 8.12/2.72  tff(c_2753, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_2730])).
% 8.12/2.72  tff(c_2755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2668, c_2753])).
% 8.12/2.72  tff(c_2757, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2640])).
% 8.12/2.72  tff(c_1550, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_149])).
% 8.12/2.72  tff(c_2761, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2757, c_1550])).
% 8.12/2.72  tff(c_2802, plain, (![A_304, C_305, B_306]: (k6_partfun1(A_304)=k5_relat_1(C_305, k2_funct_1(C_305)) | k1_xboole_0=B_306 | ~v2_funct_1(C_305) | k2_relset_1(A_304, B_306, C_305)!=B_306 | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_304, B_306))) | ~v1_funct_2(C_305, A_304, B_306) | ~v1_funct_1(C_305))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.12/2.72  tff(c_2808, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2802])).
% 8.12/2.72  tff(c_2818, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2761, c_2559, c_2808])).
% 8.12/2.72  tff(c_2819, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_2818])).
% 8.12/2.72  tff(c_2837, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2819, c_72])).
% 8.12/2.72  tff(c_2844, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_64, c_2559, c_2837])).
% 8.12/2.72  tff(c_2873, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2844, c_75])).
% 8.12/2.72  tff(c_2890, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_2873])).
% 8.12/2.72  tff(c_2558, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(splitRight, [status(thm)], [c_1557])).
% 8.12/2.72  tff(c_2758, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k5_relat_1(B_6, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_2757, c_2558])).
% 8.12/2.72  tff(c_5124, plain, (![B_412]: (k2_funct_1('#skF_4')=B_412 | k5_relat_1(B_412, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_412)!='#skF_2' | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(demodulation, [status(thm), theory('equality')], [c_2890, c_2758])).
% 8.12/2.72  tff(c_5220, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_122, c_5124])).
% 8.12/2.72  tff(c_5311, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_148, c_2655, c_5220])).
% 8.12/2.72  tff(c_5314, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5311, c_2819])).
% 8.12/2.72  tff(c_5317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1548, c_5314])).
% 8.12/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/2.72  
% 8.12/2.72  Inference rules
% 8.12/2.72  ----------------------
% 8.12/2.72  #Ref     : 0
% 8.12/2.72  #Sup     : 1104
% 8.12/2.72  #Fact    : 0
% 8.12/2.72  #Define  : 0
% 8.12/2.72  #Split   : 30
% 8.12/2.72  #Chain   : 0
% 8.12/2.72  #Close   : 0
% 8.12/2.72  
% 8.12/2.72  Ordering : KBO
% 8.12/2.72  
% 8.12/2.72  Simplification rules
% 8.12/2.72  ----------------------
% 8.12/2.72  #Subsume      : 68
% 8.12/2.72  #Demod        : 1867
% 8.12/2.72  #Tautology    : 319
% 8.12/2.72  #SimpNegUnit  : 129
% 8.12/2.72  #BackRed      : 51
% 8.12/2.72  
% 8.12/2.72  #Partial instantiations: 0
% 8.12/2.72  #Strategies tried      : 1
% 8.12/2.72  
% 8.12/2.72  Timing (in seconds)
% 8.12/2.72  ----------------------
% 8.12/2.72  Preprocessing        : 0.39
% 8.12/2.72  Parsing              : 0.20
% 8.12/2.72  CNF conversion       : 0.03
% 8.12/2.72  Main loop            : 1.54
% 8.18/2.72  Inferencing          : 0.49
% 8.18/2.72  Reduction            : 0.64
% 8.18/2.72  Demodulation         : 0.49
% 8.18/2.72  BG Simplification    : 0.05
% 8.18/2.72  Subsumption          : 0.26
% 8.18/2.72  Abstraction          : 0.07
% 8.18/2.72  MUC search           : 0.00
% 8.18/2.72  Cooper               : 0.00
% 8.18/2.72  Total                : 1.98
% 8.18/2.72  Index Insertion      : 0.00
% 8.18/2.72  Index Deletion       : 0.00
% 8.18/2.72  Index Matching       : 0.00
% 8.18/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
