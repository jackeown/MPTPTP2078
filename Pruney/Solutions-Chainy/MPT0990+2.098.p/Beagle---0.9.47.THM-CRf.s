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
% DateTime   : Thu Dec  3 10:13:10 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  171 (1156 expanded)
%              Number of leaves         :   39 ( 420 expanded)
%              Depth                    :   23
%              Number of atoms          :  429 (4743 expanded)
%              Number of equality atoms :  167 (1720 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_102,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

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

tff(c_297,plain,(
    ! [B_87,E_88,F_89,D_91,C_86,A_90] :
      ( k1_partfun1(A_90,B_87,C_86,D_91,E_88,F_89) = k5_relat_1(E_88,F_89)
      | ~ m1_subset_1(F_89,k1_zfmisc_1(k2_zfmisc_1(C_86,D_91)))
      | ~ v1_funct_1(F_89)
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_87)))
      | ~ v1_funct_1(E_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_303,plain,(
    ! [A_90,B_87,E_88] :
      ( k1_partfun1(A_90,B_87,'#skF_2','#skF_1',E_88,'#skF_4') = k5_relat_1(E_88,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_87)))
      | ~ v1_funct_1(E_88) ) ),
    inference(resolution,[status(thm)],[c_60,c_297])).

tff(c_462,plain,(
    ! [A_101,B_102,E_103] :
      ( k1_partfun1(A_101,B_102,'#skF_2','#skF_1',E_103,'#skF_4') = k5_relat_1(E_103,'#skF_4')
      | ~ m1_subset_1(E_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_1(E_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_303])).

tff(c_468,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_462])).

tff(c_475,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_468])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_170,plain,(
    ! [D_63,C_64,A_65,B_66] :
      ( D_63 = C_64
      | ~ r2_relset_1(A_65,B_66,C_64,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_178,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_170])).

tff(c_193,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_178])).

tff(c_212,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_482,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_212])).

tff(c_493,plain,(
    ! [D_108,C_105,F_107,E_106,B_109,A_104] :
      ( m1_subset_1(k1_partfun1(A_104,B_109,C_105,D_108,E_106,F_107),k1_zfmisc_1(k2_zfmisc_1(A_104,D_108)))
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_105,D_108)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_109)))
      | ~ v1_funct_1(E_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_524,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_493])).

tff(c_543,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_524])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_543])).

tff(c_549,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_594,plain,(
    ! [E_115,A_113,B_118,C_114,F_116,D_117] :
      ( v1_funct_1(k1_partfun1(A_113,B_118,C_114,D_117,E_115,F_116))
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_114,D_117)))
      | ~ v1_funct_1(F_116)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_118)))
      | ~ v1_funct_1(E_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_600,plain,(
    ! [A_113,B_118,E_115] :
      ( v1_funct_1(k1_partfun1(A_113,B_118,'#skF_2','#skF_1',E_115,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_118)))
      | ~ v1_funct_1(E_115) ) ),
    inference(resolution,[status(thm)],[c_60,c_594])).

tff(c_608,plain,(
    ! [A_119,B_120,E_121] :
      ( v1_funct_1(k1_partfun1(A_119,B_120,'#skF_2','#skF_1',E_121,'#skF_4'))
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_600])).

tff(c_614,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_608])).

tff(c_621,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_549,c_614])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4])).

tff(c_6,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_2] : v1_relat_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_113,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_113])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_138,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_144,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_138])).

tff(c_151,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_144])).

tff(c_14,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_relat_1(k2_relat_1(A_4)) != k5_relat_1(B_6,A_4)
      | k2_relat_1(B_6) != k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_558,plain,(
    ! [A_110,B_111] :
      ( k2_funct_1(A_110) = B_111
      | k6_partfun1(k2_relat_1(A_110)) != k5_relat_1(B_111,A_110)
      | k2_relat_1(B_111) != k1_relat_1(A_110)
      | ~ v2_funct_1(A_110)
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_564,plain,(
    ! [B_111] :
      ( k2_funct_1('#skF_3') = B_111
      | k5_relat_1(B_111,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_111) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_558])).

tff(c_573,plain,(
    ! [B_112] :
      ( k2_funct_1('#skF_3') = B_112
      | k5_relat_1(B_112,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_112) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_70,c_54,c_564])).

tff(c_582,plain,(
    ! [A_2] :
      ( k6_partfun1(A_2) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_2),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_2)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_2)) ) ),
    inference(resolution,[status(thm)],[c_76,c_573])).

tff(c_659,plain,(
    ! [A_133] :
      ( k6_partfun1(A_133) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_133),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_133
      | ~ v1_funct_1(k6_partfun1(A_133)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_582])).

tff(c_663,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_621,c_659])).

tff(c_664,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_663])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_696,plain,(
    ! [A_138,C_139,B_140] :
      ( k6_partfun1(A_138) = k5_relat_1(C_139,k2_funct_1(C_139))
      | k1_xboole_0 = B_140
      | ~ v2_funct_1(C_139)
      | k2_relset_1(A_138,B_140,C_139) != B_140
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_140)))
      | ~ v1_funct_2(C_139,A_138,B_140)
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_700,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_696])).

tff(c_708,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_700])).

tff(c_709,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_708])).

tff(c_12,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_717,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_73])).

tff(c_724,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_70,c_54,c_717])).

tff(c_754,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_78])).

tff(c_775,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_754])).

tff(c_777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_664,c_775])).

tff(c_779,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_663])).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_126,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_113])).

tff(c_576,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_573])).

tff(c_585,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_576])).

tff(c_586,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_585])).

tff(c_592,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_782,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_592])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_127,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_134,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_71,c_127])).

tff(c_152,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_138])).

tff(c_1379,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k2_relset_1(A_171,B_172,C_173) = B_172
      | ~ r2_relset_1(B_172,B_172,k1_partfun1(B_172,A_171,A_171,B_172,D_174,C_173),k6_partfun1(B_172))
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(B_172,A_171)))
      | ~ v1_funct_2(D_174,B_172,A_171)
      | ~ v1_funct_1(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(C_173,A_171,B_172)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1385,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_1379])).

tff(c_1389,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_134,c_152,c_1385])).

tff(c_1391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_782,c_1389])).

tff(c_1392,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_2322,plain,(
    ! [A_268,E_266,C_264,B_265,F_267,D_269] :
      ( k1_partfun1(A_268,B_265,C_264,D_269,E_266,F_267) = k5_relat_1(E_266,F_267)
      | ~ m1_subset_1(F_267,k1_zfmisc_1(k2_zfmisc_1(C_264,D_269)))
      | ~ v1_funct_1(F_267)
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_268,B_265)))
      | ~ v1_funct_1(E_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2328,plain,(
    ! [A_268,B_265,E_266] :
      ( k1_partfun1(A_268,B_265,'#skF_2','#skF_1',E_266,'#skF_4') = k5_relat_1(E_266,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_268,B_265)))
      | ~ v1_funct_1(E_266) ) ),
    inference(resolution,[status(thm)],[c_60,c_2322])).

tff(c_2341,plain,(
    ! [A_271,B_272,E_273] :
      ( k1_partfun1(A_271,B_272,'#skF_2','#skF_1',E_273,'#skF_4') = k5_relat_1(E_273,'#skF_4')
      | ~ m1_subset_1(E_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272)))
      | ~ v1_funct_1(E_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2328])).

tff(c_2347,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2341])).

tff(c_2354,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_549,c_2347])).

tff(c_1393,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_72,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_partfun1(k2_relat_1(A_4)) != k5_relat_1(B_6,A_4)
      | k2_relat_1(B_6) != k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_1397,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1393,c_72])).

tff(c_1401,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_1397])).

tff(c_1409,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1401])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_2240,plain,(
    ! [E_244,D_245,A_243,C_247,B_246] :
      ( k1_xboole_0 = C_247
      | v2_funct_1(E_244)
      | k2_relset_1(A_243,B_246,D_245) != B_246
      | ~ v2_funct_1(k1_partfun1(A_243,B_246,B_246,C_247,D_245,E_244))
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(B_246,C_247)))
      | ~ v1_funct_2(E_244,B_246,C_247)
      | ~ v1_funct_1(E_244)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_246)))
      | ~ v1_funct_2(D_245,A_243,B_246)
      | ~ v1_funct_1(D_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2246,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_549,c_2240])).

tff(c_2254,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_75,c_58,c_2246])).

tff(c_2256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1409,c_52,c_2254])).

tff(c_2258,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1401])).

tff(c_2273,plain,(
    ! [C_252,B_256,F_254,E_253,D_255,A_251] :
      ( v1_funct_1(k1_partfun1(A_251,B_256,C_252,D_255,E_253,F_254))
      | ~ m1_subset_1(F_254,k1_zfmisc_1(k2_zfmisc_1(C_252,D_255)))
      | ~ v1_funct_1(F_254)
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_256)))
      | ~ v1_funct_1(E_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2279,plain,(
    ! [A_251,B_256,E_253] :
      ( v1_funct_1(k1_partfun1(A_251,B_256,'#skF_2','#skF_1',E_253,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_256)))
      | ~ v1_funct_1(E_253) ) ),
    inference(resolution,[status(thm)],[c_60,c_2273])).

tff(c_2305,plain,(
    ! [A_261,B_262,E_263] :
      ( v1_funct_1(k1_partfun1(A_261,B_262,'#skF_2','#skF_1',E_263,'#skF_4'))
      | ~ m1_subset_1(E_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_1(E_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2279])).

tff(c_2311,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2305])).

tff(c_2318,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_549,c_2311])).

tff(c_591,plain,(
    ! [A_2] :
      ( k6_partfun1(A_2) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_2),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_2
      | ~ v1_funct_1(k6_partfun1(A_2)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_582])).

tff(c_2339,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2318,c_591])).

tff(c_2367,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2339])).

tff(c_2368,plain,(
    ! [A_274,C_275,B_276] :
      ( k6_partfun1(A_274) = k5_relat_1(C_275,k2_funct_1(C_275))
      | k1_xboole_0 = B_276
      | ~ v2_funct_1(C_275)
      | k2_relset_1(A_274,B_276,C_275) != B_276
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_274,B_276)))
      | ~ v1_funct_2(C_275,A_274,B_276)
      | ~ v1_funct_1(C_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2372,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2368])).

tff(c_2380,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_2372])).

tff(c_2381,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2380])).

tff(c_2389,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_73])).

tff(c_2396,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_70,c_54,c_2389])).

tff(c_2427,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2396,c_78])).

tff(c_2448,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2427])).

tff(c_2450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2367,c_2448])).

tff(c_2452,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2339])).

tff(c_1394,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1393,c_152])).

tff(c_2456,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_1394])).

tff(c_2497,plain,(
    ! [A_280,C_281,B_282] :
      ( k6_partfun1(A_280) = k5_relat_1(C_281,k2_funct_1(C_281))
      | k1_xboole_0 = B_282
      | ~ v2_funct_1(C_281)
      | k2_relset_1(A_280,B_282,C_281) != B_282
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_280,B_282)))
      | ~ v1_funct_2(C_281,A_280,B_282)
      | ~ v1_funct_1(C_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2503,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_2497])).

tff(c_2513,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_2456,c_2258,c_2503])).

tff(c_2514,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2513])).

tff(c_2532,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2514,c_73])).

tff(c_2539,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_2258,c_2532])).

tff(c_2566,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2539,c_78])).

tff(c_2581,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2566])).

tff(c_2257,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(splitRight,[status(thm)],[c_1401])).

tff(c_2453,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k5_relat_1(B_6,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_2257])).

tff(c_4649,plain,(
    ! [B_382] :
      ( k2_funct_1('#skF_4') = B_382
      | k5_relat_1(B_382,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_382) != '#skF_2'
      | ~ v1_funct_1(B_382)
      | ~ v1_relat_1(B_382) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2581,c_2453])).

tff(c_4742,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_4649])).

tff(c_4834,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_151,c_2354,c_4742])).

tff(c_5001,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4834,c_2514])).

tff(c_5004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1392,c_5001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.33  % CPULimit   : 60
% 0.18/0.33  % DateTime   : Tue Dec  1 19:18:07 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.15/2.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.52  
% 7.15/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.52  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.15/2.52  
% 7.15/2.52  %Foreground sorts:
% 7.15/2.52  
% 7.15/2.52  
% 7.15/2.52  %Background operators:
% 7.15/2.52  
% 7.15/2.52  
% 7.15/2.52  %Foreground operators:
% 7.15/2.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.15/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.15/2.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.15/2.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.15/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.15/2.52  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.15/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.15/2.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.15/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.15/2.52  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.15/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.15/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.15/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.15/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.15/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.15/2.52  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.15/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.15/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.15/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.15/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.15/2.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.15/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.15/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.15/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.15/2.52  
% 7.15/2.54  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.15/2.54  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.15/2.54  tff(f_102, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.15/2.54  tff(f_78, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.15/2.54  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.15/2.54  tff(f_90, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.15/2.54  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.15/2.54  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.15/2.54  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.15/2.54  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.15/2.54  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 7.15/2.54  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.15/2.54  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.15/2.54  tff(f_119, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.15/2.54  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.15/2.54  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_297, plain, (![B_87, E_88, F_89, D_91, C_86, A_90]: (k1_partfun1(A_90, B_87, C_86, D_91, E_88, F_89)=k5_relat_1(E_88, F_89) | ~m1_subset_1(F_89, k1_zfmisc_1(k2_zfmisc_1(C_86, D_91))) | ~v1_funct_1(F_89) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_87))) | ~v1_funct_1(E_88))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.15/2.54  tff(c_303, plain, (![A_90, B_87, E_88]: (k1_partfun1(A_90, B_87, '#skF_2', '#skF_1', E_88, '#skF_4')=k5_relat_1(E_88, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_87))) | ~v1_funct_1(E_88))), inference(resolution, [status(thm)], [c_60, c_297])).
% 7.15/2.54  tff(c_462, plain, (![A_101, B_102, E_103]: (k1_partfun1(A_101, B_102, '#skF_2', '#skF_1', E_103, '#skF_4')=k5_relat_1(E_103, '#skF_4') | ~m1_subset_1(E_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_1(E_103))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_303])).
% 7.15/2.54  tff(c_468, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_462])).
% 7.15/2.54  tff(c_475, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_468])).
% 7.15/2.54  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.15/2.54  tff(c_24, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.15/2.54  tff(c_71, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24])).
% 7.15/2.54  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_170, plain, (![D_63, C_64, A_65, B_66]: (D_63=C_64 | ~r2_relset_1(A_65, B_66, C_64, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.15/2.54  tff(c_178, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_170])).
% 7.15/2.54  tff(c_193, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_178])).
% 7.15/2.54  tff(c_212, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_193])).
% 7.15/2.54  tff(c_482, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_212])).
% 7.15/2.54  tff(c_493, plain, (![D_108, C_105, F_107, E_106, B_109, A_104]: (m1_subset_1(k1_partfun1(A_104, B_109, C_105, D_108, E_106, F_107), k1_zfmisc_1(k2_zfmisc_1(A_104, D_108))) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_105, D_108))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_109))) | ~v1_funct_1(E_106))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.54  tff(c_524, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_475, c_493])).
% 7.15/2.54  tff(c_543, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_524])).
% 7.15/2.54  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_482, c_543])).
% 7.15/2.54  tff(c_549, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_193])).
% 7.15/2.54  tff(c_594, plain, (![E_115, A_113, B_118, C_114, F_116, D_117]: (v1_funct_1(k1_partfun1(A_113, B_118, C_114, D_117, E_115, F_116)) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_114, D_117))) | ~v1_funct_1(F_116) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_118))) | ~v1_funct_1(E_115))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.54  tff(c_600, plain, (![A_113, B_118, E_115]: (v1_funct_1(k1_partfun1(A_113, B_118, '#skF_2', '#skF_1', E_115, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_118))) | ~v1_funct_1(E_115))), inference(resolution, [status(thm)], [c_60, c_594])).
% 7.15/2.54  tff(c_608, plain, (![A_119, B_120, E_121]: (v1_funct_1(k1_partfun1(A_119, B_120, '#skF_2', '#skF_1', E_121, '#skF_4')) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_121))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_600])).
% 7.15/2.54  tff(c_614, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_608])).
% 7.15/2.54  tff(c_621, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_549, c_614])).
% 7.15/2.54  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.15/2.54  tff(c_77, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4])).
% 7.15/2.54  tff(c_6, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.15/2.54  tff(c_76, plain, (![A_2]: (v1_relat_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 7.15/2.54  tff(c_113, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.15/2.54  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_113])).
% 7.15/2.54  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_138, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.15/2.54  tff(c_144, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_138])).
% 7.15/2.54  tff(c_151, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_144])).
% 7.15/2.54  tff(c_14, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.15/2.54  tff(c_558, plain, (![A_110, B_111]: (k2_funct_1(A_110)=B_111 | k6_partfun1(k2_relat_1(A_110))!=k5_relat_1(B_111, A_110) | k2_relat_1(B_111)!=k1_relat_1(A_110) | ~v2_funct_1(A_110) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 7.15/2.54  tff(c_564, plain, (![B_111]: (k2_funct_1('#skF_3')=B_111 | k5_relat_1(B_111, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_111)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_111) | ~v1_relat_1(B_111) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_558])).
% 7.15/2.54  tff(c_573, plain, (![B_112]: (k2_funct_1('#skF_3')=B_112 | k5_relat_1(B_112, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_112)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_70, c_54, c_564])).
% 7.15/2.54  tff(c_582, plain, (![A_2]: (k6_partfun1(A_2)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_2), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_2))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_2)))), inference(resolution, [status(thm)], [c_76, c_573])).
% 7.15/2.54  tff(c_659, plain, (![A_133]: (k6_partfun1(A_133)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_133), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_133 | ~v1_funct_1(k6_partfun1(A_133)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_582])).
% 7.15/2.54  tff(c_663, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_621, c_659])).
% 7.15/2.54  tff(c_664, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_663])).
% 7.15/2.54  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.15/2.54  tff(c_78, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2])).
% 7.15/2.54  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_696, plain, (![A_138, C_139, B_140]: (k6_partfun1(A_138)=k5_relat_1(C_139, k2_funct_1(C_139)) | k1_xboole_0=B_140 | ~v2_funct_1(C_139) | k2_relset_1(A_138, B_140, C_139)!=B_140 | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_140))) | ~v1_funct_2(C_139, A_138, B_140) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.15/2.54  tff(c_700, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_696])).
% 7.15/2.54  tff(c_708, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_700])).
% 7.15/2.54  tff(c_709, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_708])).
% 7.15/2.54  tff(c_12, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.15/2.54  tff(c_73, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 7.15/2.54  tff(c_717, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_709, c_73])).
% 7.15/2.54  tff(c_724, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_70, c_54, c_717])).
% 7.15/2.54  tff(c_754, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_724, c_78])).
% 7.15/2.54  tff(c_775, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_754])).
% 7.15/2.54  tff(c_777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_664, c_775])).
% 7.15/2.54  tff(c_779, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_663])).
% 7.15/2.54  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_126, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_113])).
% 7.15/2.54  tff(c_576, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_126, c_573])).
% 7.15/2.54  tff(c_585, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_576])).
% 7.15/2.54  tff(c_586, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_585])).
% 7.15/2.54  tff(c_592, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_586])).
% 7.15/2.54  tff(c_782, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_779, c_592])).
% 7.15/2.54  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_127, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.15/2.54  tff(c_134, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_71, c_127])).
% 7.15/2.54  tff(c_152, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_138])).
% 7.15/2.54  tff(c_1379, plain, (![A_171, B_172, C_173, D_174]: (k2_relset_1(A_171, B_172, C_173)=B_172 | ~r2_relset_1(B_172, B_172, k1_partfun1(B_172, A_171, A_171, B_172, D_174, C_173), k6_partfun1(B_172)) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(B_172, A_171))) | ~v1_funct_2(D_174, B_172, A_171) | ~v1_funct_1(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(C_173, A_171, B_172) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.15/2.54  tff(c_1385, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_549, c_1379])).
% 7.15/2.54  tff(c_1389, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_134, c_152, c_1385])).
% 7.15/2.54  tff(c_1391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_782, c_1389])).
% 7.15/2.54  tff(c_1392, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_586])).
% 7.15/2.54  tff(c_2322, plain, (![A_268, E_266, C_264, B_265, F_267, D_269]: (k1_partfun1(A_268, B_265, C_264, D_269, E_266, F_267)=k5_relat_1(E_266, F_267) | ~m1_subset_1(F_267, k1_zfmisc_1(k2_zfmisc_1(C_264, D_269))) | ~v1_funct_1(F_267) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_268, B_265))) | ~v1_funct_1(E_266))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.15/2.54  tff(c_2328, plain, (![A_268, B_265, E_266]: (k1_partfun1(A_268, B_265, '#skF_2', '#skF_1', E_266, '#skF_4')=k5_relat_1(E_266, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_268, B_265))) | ~v1_funct_1(E_266))), inference(resolution, [status(thm)], [c_60, c_2322])).
% 7.15/2.54  tff(c_2341, plain, (![A_271, B_272, E_273]: (k1_partfun1(A_271, B_272, '#skF_2', '#skF_1', E_273, '#skF_4')=k5_relat_1(E_273, '#skF_4') | ~m1_subset_1(E_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))) | ~v1_funct_1(E_273))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2328])).
% 7.15/2.54  tff(c_2347, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2341])).
% 7.15/2.54  tff(c_2354, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_549, c_2347])).
% 7.15/2.54  tff(c_1393, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_586])).
% 7.15/2.54  tff(c_72, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_partfun1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 7.15/2.54  tff(c_1397, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1393, c_72])).
% 7.15/2.54  tff(c_1401, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_1397])).
% 7.15/2.54  tff(c_1409, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1401])).
% 7.15/2.54  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_187])).
% 7.15/2.54  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.15/2.54  tff(c_75, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 7.15/2.54  tff(c_2240, plain, (![E_244, D_245, A_243, C_247, B_246]: (k1_xboole_0=C_247 | v2_funct_1(E_244) | k2_relset_1(A_243, B_246, D_245)!=B_246 | ~v2_funct_1(k1_partfun1(A_243, B_246, B_246, C_247, D_245, E_244)) | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(B_246, C_247))) | ~v1_funct_2(E_244, B_246, C_247) | ~v1_funct_1(E_244) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_246))) | ~v1_funct_2(D_245, A_243, B_246) | ~v1_funct_1(D_245))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.15/2.54  tff(c_2246, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_549, c_2240])).
% 7.15/2.54  tff(c_2254, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_75, c_58, c_2246])).
% 7.15/2.54  tff(c_2256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1409, c_52, c_2254])).
% 7.15/2.54  tff(c_2258, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1401])).
% 7.15/2.54  tff(c_2273, plain, (![C_252, B_256, F_254, E_253, D_255, A_251]: (v1_funct_1(k1_partfun1(A_251, B_256, C_252, D_255, E_253, F_254)) | ~m1_subset_1(F_254, k1_zfmisc_1(k2_zfmisc_1(C_252, D_255))) | ~v1_funct_1(F_254) | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_256))) | ~v1_funct_1(E_253))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.15/2.54  tff(c_2279, plain, (![A_251, B_256, E_253]: (v1_funct_1(k1_partfun1(A_251, B_256, '#skF_2', '#skF_1', E_253, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_256))) | ~v1_funct_1(E_253))), inference(resolution, [status(thm)], [c_60, c_2273])).
% 7.15/2.54  tff(c_2305, plain, (![A_261, B_262, E_263]: (v1_funct_1(k1_partfun1(A_261, B_262, '#skF_2', '#skF_1', E_263, '#skF_4')) | ~m1_subset_1(E_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_1(E_263))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2279])).
% 7.15/2.54  tff(c_2311, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2305])).
% 7.15/2.54  tff(c_2318, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_549, c_2311])).
% 7.15/2.54  tff(c_591, plain, (![A_2]: (k6_partfun1(A_2)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_2), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_2 | ~v1_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_582])).
% 7.15/2.54  tff(c_2339, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2318, c_591])).
% 7.15/2.54  tff(c_2367, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2339])).
% 7.15/2.54  tff(c_2368, plain, (![A_274, C_275, B_276]: (k6_partfun1(A_274)=k5_relat_1(C_275, k2_funct_1(C_275)) | k1_xboole_0=B_276 | ~v2_funct_1(C_275) | k2_relset_1(A_274, B_276, C_275)!=B_276 | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_274, B_276))) | ~v1_funct_2(C_275, A_274, B_276) | ~v1_funct_1(C_275))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.15/2.54  tff(c_2372, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2368])).
% 7.15/2.54  tff(c_2380, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_2372])).
% 7.15/2.54  tff(c_2381, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_2380])).
% 7.15/2.54  tff(c_2389, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2381, c_73])).
% 7.15/2.54  tff(c_2396, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_70, c_54, c_2389])).
% 7.15/2.54  tff(c_2427, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2396, c_78])).
% 7.15/2.54  tff(c_2448, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2427])).
% 7.15/2.54  tff(c_2450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2367, c_2448])).
% 7.15/2.54  tff(c_2452, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2339])).
% 7.15/2.54  tff(c_1394, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1393, c_152])).
% 7.15/2.54  tff(c_2456, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_1394])).
% 7.15/2.54  tff(c_2497, plain, (![A_280, C_281, B_282]: (k6_partfun1(A_280)=k5_relat_1(C_281, k2_funct_1(C_281)) | k1_xboole_0=B_282 | ~v2_funct_1(C_281) | k2_relset_1(A_280, B_282, C_281)!=B_282 | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_280, B_282))) | ~v1_funct_2(C_281, A_280, B_282) | ~v1_funct_1(C_281))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.15/2.54  tff(c_2503, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_2497])).
% 7.15/2.54  tff(c_2513, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_2456, c_2258, c_2503])).
% 7.15/2.54  tff(c_2514, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_2513])).
% 7.15/2.54  tff(c_2532, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2514, c_73])).
% 7.15/2.54  tff(c_2539, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_2258, c_2532])).
% 7.15/2.54  tff(c_2566, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2539, c_78])).
% 7.15/2.54  tff(c_2581, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2566])).
% 7.15/2.54  tff(c_2257, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(splitRight, [status(thm)], [c_1401])).
% 7.15/2.54  tff(c_2453, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k5_relat_1(B_6, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_2452, c_2257])).
% 7.15/2.54  tff(c_4649, plain, (![B_382]: (k2_funct_1('#skF_4')=B_382 | k5_relat_1(B_382, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_382)!='#skF_2' | ~v1_funct_1(B_382) | ~v1_relat_1(B_382))), inference(demodulation, [status(thm), theory('equality')], [c_2581, c_2453])).
% 7.15/2.54  tff(c_4742, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_125, c_4649])).
% 7.15/2.54  tff(c_4834, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_151, c_2354, c_4742])).
% 7.15/2.54  tff(c_5001, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4834, c_2514])).
% 7.15/2.54  tff(c_5004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1392, c_5001])).
% 7.15/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.54  
% 7.15/2.54  Inference rules
% 7.15/2.54  ----------------------
% 7.15/2.54  #Ref     : 0
% 7.15/2.54  #Sup     : 1035
% 7.15/2.54  #Fact    : 0
% 7.15/2.54  #Define  : 0
% 7.15/2.54  #Split   : 28
% 7.15/2.54  #Chain   : 0
% 7.15/2.54  #Close   : 0
% 7.15/2.54  
% 7.15/2.54  Ordering : KBO
% 7.15/2.54  
% 7.15/2.54  Simplification rules
% 7.15/2.54  ----------------------
% 7.15/2.54  #Subsume      : 59
% 7.15/2.54  #Demod        : 1724
% 7.15/2.54  #Tautology    : 290
% 7.15/2.54  #SimpNegUnit  : 114
% 7.15/2.54  #BackRed      : 48
% 7.15/2.54  
% 7.15/2.54  #Partial instantiations: 0
% 7.15/2.54  #Strategies tried      : 1
% 7.15/2.54  
% 7.15/2.54  Timing (in seconds)
% 7.15/2.54  ----------------------
% 7.15/2.55  Preprocessing        : 0.39
% 7.15/2.55  Parsing              : 0.22
% 7.15/2.55  CNF conversion       : 0.03
% 7.15/2.55  Main loop            : 1.32
% 7.15/2.55  Inferencing          : 0.40
% 7.15/2.55  Reduction            : 0.56
% 7.15/2.55  Demodulation         : 0.43
% 7.15/2.55  BG Simplification    : 0.05
% 7.15/2.55  Subsumption          : 0.23
% 7.15/2.55  Abstraction          : 0.06
% 7.15/2.55  MUC search           : 0.00
% 7.15/2.55  Cooper               : 0.00
% 7.15/2.55  Total                : 1.77
% 7.15/2.55  Index Insertion      : 0.00
% 7.15/2.55  Index Deletion       : 0.00
% 7.15/2.55  Index Matching       : 0.00
% 7.15/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
