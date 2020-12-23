%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:09 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  161 (1094 expanded)
%              Number of leaves         :   40 ( 401 expanded)
%              Depth                    :   21
%              Number of atoms          :  413 (4679 expanded)
%              Number of equality atoms :  155 (1665 expanded)
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

tff(f_189,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_163,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_121,axiom,(
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

tff(f_147,axiom,(
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

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_280,plain,(
    ! [C_85,E_87,F_88,A_89,B_86,D_90] :
      ( k1_partfun1(A_89,B_86,C_85,D_90,E_87,F_88) = k5_relat_1(E_87,F_88)
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_85,D_90)))
      | ~ v1_funct_1(F_88)
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_286,plain,(
    ! [A_89,B_86,E_87] :
      ( k1_partfun1(A_89,B_86,'#skF_2','#skF_1',E_87,'#skF_4') = k5_relat_1(E_87,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(resolution,[status(thm)],[c_62,c_280])).

tff(c_369,plain,(
    ! [A_103,B_104,E_105] :
      ( k1_partfun1(A_103,B_104,'#skF_2','#skF_1',E_105,'#skF_4') = k5_relat_1(E_105,'#skF_4')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_286])).

tff(c_375,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_369])).

tff(c_382,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_375])).

tff(c_30,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_188,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r2_relset_1(A_68,B_69,C_67,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_196,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_188])).

tff(c_211,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_196])).

tff(c_212,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_387,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_212])).

tff(c_444,plain,(
    ! [B_111,A_110,F_112,C_109,D_113,E_114] :
      ( m1_subset_1(k1_partfun1(A_110,B_111,C_109,D_113,E_114,F_112),k1_zfmisc_1(k2_zfmisc_1(A_110,D_113)))
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_109,D_113)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_478,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_444])).

tff(c_499,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_478])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_499])).

tff(c_502,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_545,plain,(
    ! [B_121,D_123,A_120,C_119,E_124,F_122] :
      ( v1_funct_1(k1_partfun1(A_120,B_121,C_119,D_123,E_124,F_122))
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_119,D_123)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_551,plain,(
    ! [A_120,B_121,E_124] :
      ( v1_funct_1(k1_partfun1(A_120,B_121,'#skF_2','#skF_1',E_124,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(E_124) ) ),
    inference(resolution,[status(thm)],[c_62,c_545])).

tff(c_576,plain,(
    ! [A_128,B_129,E_130] :
      ( v1_funct_1(k1_partfun1(A_128,B_129,'#skF_2','#skF_1',E_130,'#skF_4'))
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_551])).

tff(c_582,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_576])).

tff(c_589,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_502,c_582])).

tff(c_34,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_6,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_2] : v1_relat_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_113,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_113])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_137,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_143,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_137])).

tff(c_150,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_143])).

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

tff(c_511,plain,(
    ! [A_115,B_116] :
      ( k2_funct_1(A_115) = B_116
      | k6_partfun1(k2_relat_1(A_115)) != k5_relat_1(B_116,A_115)
      | k2_relat_1(B_116) != k1_relat_1(A_115)
      | ~ v2_funct_1(A_115)
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_515,plain,(
    ! [B_116] :
      ( k2_funct_1('#skF_3') = B_116
      | k5_relat_1(B_116,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_116) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_511])).

tff(c_522,plain,(
    ! [B_117] :
      ( k2_funct_1('#skF_3') = B_117
      | k5_relat_1(B_117,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_117) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_56,c_515])).

tff(c_531,plain,(
    ! [A_2] :
      ( k6_partfun1(A_2) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_2),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_2)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_2)) ) ),
    inference(resolution,[status(thm)],[c_75,c_522])).

tff(c_540,plain,(
    ! [A_2] :
      ( k6_partfun1(A_2) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_2),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_2
      | ~ v1_funct_1(k6_partfun1(A_2)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_531])).

tff(c_596,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_589,c_540])).

tff(c_599,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_596])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_654,plain,(
    ! [A_143,C_144,B_145] :
      ( k6_partfun1(A_143) = k5_relat_1(C_144,k2_funct_1(C_144))
      | k1_xboole_0 = B_145
      | ~ v2_funct_1(C_144)
      | k2_relset_1(A_143,B_145,C_144) != B_145
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_143,B_145)))
      | ~ v1_funct_2(C_144,A_143,B_145)
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_658,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_654])).

tff(c_666,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_658])).

tff(c_667,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_666])).

tff(c_10,plain,(
    ! [A_3] :
      ( k2_relat_1(k5_relat_1(A_3,k2_funct_1(A_3))) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_675,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_10])).

tff(c_682,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_56,c_76,c_675])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_599,c_682])).

tff(c_686,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_596])).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_126,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_113])).

tff(c_525,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_522])).

tff(c_534,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_525])).

tff(c_535,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_534])).

tff(c_541,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_689,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_541])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_127,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_134,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_30,c_127])).

tff(c_151,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_137])).

tff(c_1334,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k2_relset_1(A_191,B_192,C_193) = B_192
      | ~ r2_relset_1(B_192,B_192,k1_partfun1(B_192,A_191,A_191,B_192,D_194,C_193),k6_partfun1(B_192))
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(B_192,A_191)))
      | ~ v1_funct_2(D_194,B_192,A_191)
      | ~ v1_funct_1(D_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192)))
      | ~ v1_funct_2(C_193,A_191,B_192)
      | ~ v1_funct_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1340,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_1334])).

tff(c_1344,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_134,c_151,c_1340])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_689,c_1344])).

tff(c_1347,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_2460,plain,(
    ! [A_312,D_313,F_311,B_309,C_308,E_310] :
      ( k1_partfun1(A_312,B_309,C_308,D_313,E_310,F_311) = k5_relat_1(E_310,F_311)
      | ~ m1_subset_1(F_311,k1_zfmisc_1(k2_zfmisc_1(C_308,D_313)))
      | ~ v1_funct_1(F_311)
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(A_312,B_309)))
      | ~ v1_funct_1(E_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2466,plain,(
    ! [A_312,B_309,E_310] :
      ( k1_partfun1(A_312,B_309,'#skF_2','#skF_1',E_310,'#skF_4') = k5_relat_1(E_310,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(A_312,B_309)))
      | ~ v1_funct_1(E_310) ) ),
    inference(resolution,[status(thm)],[c_62,c_2460])).

tff(c_2479,plain,(
    ! [A_315,B_316,E_317] :
      ( k1_partfun1(A_315,B_316,'#skF_2','#skF_1',E_317,'#skF_4') = k5_relat_1(E_317,'#skF_4')
      | ~ m1_subset_1(E_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316)))
      | ~ v1_funct_1(E_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2466])).

tff(c_2485,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2479])).

tff(c_2492,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_502,c_2485])).

tff(c_1348,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_73,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_partfun1(k2_relat_1(A_4)) != k5_relat_1(B_6,A_4)
      | k2_relat_1(B_6) != k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_1352,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1348,c_73])).

tff(c_1356,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_66,c_1352])).

tff(c_1364,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1356])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_2385,plain,(
    ! [D_289,B_290,A_287,C_291,E_288] :
      ( k1_xboole_0 = C_291
      | v2_funct_1(E_288)
      | k2_relset_1(A_287,B_290,D_289) != B_290
      | ~ v2_funct_1(k1_partfun1(A_287,B_290,B_290,C_291,D_289,E_288))
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(B_290,C_291)))
      | ~ v1_funct_2(E_288,B_290,C_291)
      | ~ v1_funct_1(E_288)
      | ~ m1_subset_1(D_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_290)))
      | ~ v1_funct_2(D_289,A_287,B_290)
      | ~ v1_funct_1(D_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2393,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_502,c_2385])).

tff(c_2404,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_74,c_60,c_2393])).

tff(c_2406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1364,c_54,c_2404])).

tff(c_2408,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1356])).

tff(c_2411,plain,(
    ! [A_296,B_297,D_299,E_300,C_295,F_298] :
      ( v1_funct_1(k1_partfun1(A_296,B_297,C_295,D_299,E_300,F_298))
      | ~ m1_subset_1(F_298,k1_zfmisc_1(k2_zfmisc_1(C_295,D_299)))
      | ~ v1_funct_1(F_298)
      | ~ m1_subset_1(E_300,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297)))
      | ~ v1_funct_1(E_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2417,plain,(
    ! [A_296,B_297,E_300] :
      ( v1_funct_1(k1_partfun1(A_296,B_297,'#skF_2','#skF_1',E_300,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_300,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297)))
      | ~ v1_funct_1(E_300) ) ),
    inference(resolution,[status(thm)],[c_62,c_2411])).

tff(c_2443,plain,(
    ! [A_305,B_306,E_307] :
      ( v1_funct_1(k1_partfun1(A_305,B_306,'#skF_2','#skF_1',E_307,'#skF_4'))
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | ~ v1_funct_1(E_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2417])).

tff(c_2449,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2443])).

tff(c_2456,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_502,c_2449])).

tff(c_2477,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2456,c_540])).

tff(c_2505,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2477])).

tff(c_2506,plain,(
    ! [A_318,C_319,B_320] :
      ( k6_partfun1(A_318) = k5_relat_1(C_319,k2_funct_1(C_319))
      | k1_xboole_0 = B_320
      | ~ v2_funct_1(C_319)
      | k2_relset_1(A_318,B_320,C_319) != B_320
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_318,B_320)))
      | ~ v1_funct_2(C_319,A_318,B_320)
      | ~ v1_funct_1(C_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2510,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2506])).

tff(c_2518,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_2510])).

tff(c_2519,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2518])).

tff(c_2527,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_10])).

tff(c_2534,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_72,c_56,c_76,c_2527])).

tff(c_2536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2505,c_2534])).

tff(c_2538,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2477])).

tff(c_1349,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_151])).

tff(c_2542,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_1349])).

tff(c_2588,plain,(
    ! [A_324,C_325,B_326] :
      ( k6_partfun1(A_324) = k5_relat_1(C_325,k2_funct_1(C_325))
      | k1_xboole_0 = B_326
      | ~ v2_funct_1(C_325)
      | k2_relset_1(A_324,B_326,C_325) != B_326
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_324,B_326)))
      | ~ v1_funct_2(C_325,A_324,B_326)
      | ~ v1_funct_1(C_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2594,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2588])).

tff(c_2604,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2542,c_2408,c_2594])).

tff(c_2605,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2604])).

tff(c_2623,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2605,c_10])).

tff(c_2630,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_66,c_2408,c_76,c_2623])).

tff(c_2407,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(splitRight,[status(thm)],[c_1356])).

tff(c_2539,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k5_relat_1(B_6,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2538,c_2407])).

tff(c_4491,plain,(
    ! [B_418] :
      ( k2_funct_1('#skF_4') = B_418
      | k5_relat_1(B_418,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_418) != '#skF_2'
      | ~ v1_funct_1(B_418)
      | ~ v1_relat_1(B_418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2630,c_2539])).

tff(c_4584,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_4491])).

tff(c_4676,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_150,c_2492,c_4584])).

tff(c_4683,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4676,c_2605])).

tff(c_4686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1347,c_4683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/2.51  
% 7.23/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.23/2.51  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.23/2.51  
% 7.23/2.51  %Foreground sorts:
% 7.23/2.51  
% 7.23/2.51  
% 7.23/2.51  %Background operators:
% 7.23/2.51  
% 7.23/2.51  
% 7.23/2.51  %Foreground operators:
% 7.23/2.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.23/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.23/2.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.23/2.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.23/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.23/2.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.23/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.23/2.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.23/2.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.23/2.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.23/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.23/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.23/2.51  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.23/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.23/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.23/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.23/2.51  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.23/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.23/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.23/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.23/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.23/2.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.23/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.23/2.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.23/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.23/2.51  
% 7.54/2.56  tff(f_189, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.54/2.56  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.54/2.56  tff(f_92, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.54/2.56  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.54/2.56  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.54/2.56  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.54/2.56  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.54/2.56  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.54/2.56  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.54/2.56  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.54/2.56  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 7.54/2.56  tff(f_163, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.54/2.56  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 7.54/2.56  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.54/2.56  tff(f_147, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.54/2.56  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_280, plain, (![C_85, E_87, F_88, A_89, B_86, D_90]: (k1_partfun1(A_89, B_86, C_85, D_90, E_87, F_88)=k5_relat_1(E_87, F_88) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_85, D_90))) | ~v1_funct_1(F_88) | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_86))) | ~v1_funct_1(E_87))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.54/2.56  tff(c_286, plain, (![A_89, B_86, E_87]: (k1_partfun1(A_89, B_86, '#skF_2', '#skF_1', E_87, '#skF_4')=k5_relat_1(E_87, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_86))) | ~v1_funct_1(E_87))), inference(resolution, [status(thm)], [c_62, c_280])).
% 7.54/2.56  tff(c_369, plain, (![A_103, B_104, E_105]: (k1_partfun1(A_103, B_104, '#skF_2', '#skF_1', E_105, '#skF_4')=k5_relat_1(E_105, '#skF_4') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(E_105))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_286])).
% 7.54/2.56  tff(c_375, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_369])).
% 7.54/2.56  tff(c_382, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_375])).
% 7.54/2.56  tff(c_30, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.54/2.56  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_188, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r2_relset_1(A_68, B_69, C_67, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.54/2.56  tff(c_196, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_188])).
% 7.54/2.56  tff(c_211, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_196])).
% 7.54/2.56  tff(c_212, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_211])).
% 7.54/2.56  tff(c_387, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_212])).
% 7.54/2.56  tff(c_444, plain, (![B_111, A_110, F_112, C_109, D_113, E_114]: (m1_subset_1(k1_partfun1(A_110, B_111, C_109, D_113, E_114, F_112), k1_zfmisc_1(k2_zfmisc_1(A_110, D_113))) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_109, D_113))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.54/2.56  tff(c_478, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_382, c_444])).
% 7.54/2.56  tff(c_499, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_478])).
% 7.54/2.56  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_387, c_499])).
% 7.54/2.56  tff(c_502, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_211])).
% 7.54/2.56  tff(c_545, plain, (![B_121, D_123, A_120, C_119, E_124, F_122]: (v1_funct_1(k1_partfun1(A_120, B_121, C_119, D_123, E_124, F_122)) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_119, D_123))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.54/2.56  tff(c_551, plain, (![A_120, B_121, E_124]: (v1_funct_1(k1_partfun1(A_120, B_121, '#skF_2', '#skF_1', E_124, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(E_124))), inference(resolution, [status(thm)], [c_62, c_545])).
% 7.54/2.56  tff(c_576, plain, (![A_128, B_129, E_130]: (v1_funct_1(k1_partfun1(A_128, B_129, '#skF_2', '#skF_1', E_130, '#skF_4')) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_551])).
% 7.54/2.56  tff(c_582, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_576])).
% 7.54/2.56  tff(c_589, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_502, c_582])).
% 7.54/2.56  tff(c_34, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.54/2.56  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.54/2.56  tff(c_76, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4])).
% 7.54/2.56  tff(c_6, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.54/2.56  tff(c_75, plain, (![A_2]: (v1_relat_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 7.54/2.56  tff(c_113, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.54/2.56  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_113])).
% 7.54/2.56  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_137, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.54/2.56  tff(c_143, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_137])).
% 7.54/2.56  tff(c_150, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_143])).
% 7.54/2.56  tff(c_14, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.54/2.56  tff(c_511, plain, (![A_115, B_116]: (k2_funct_1(A_115)=B_116 | k6_partfun1(k2_relat_1(A_115))!=k5_relat_1(B_116, A_115) | k2_relat_1(B_116)!=k1_relat_1(A_115) | ~v2_funct_1(A_115) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 7.54/2.56  tff(c_515, plain, (![B_116]: (k2_funct_1('#skF_3')=B_116 | k5_relat_1(B_116, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_116)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_511])).
% 7.54/2.56  tff(c_522, plain, (![B_117]: (k2_funct_1('#skF_3')=B_117 | k5_relat_1(B_117, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_117)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_56, c_515])).
% 7.54/2.56  tff(c_531, plain, (![A_2]: (k6_partfun1(A_2)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_2), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_2))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_2)))), inference(resolution, [status(thm)], [c_75, c_522])).
% 7.54/2.56  tff(c_540, plain, (![A_2]: (k6_partfun1(A_2)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_2), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_2 | ~v1_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_531])).
% 7.54/2.56  tff(c_596, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_589, c_540])).
% 7.54/2.56  tff(c_599, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_596])).
% 7.54/2.56  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_654, plain, (![A_143, C_144, B_145]: (k6_partfun1(A_143)=k5_relat_1(C_144, k2_funct_1(C_144)) | k1_xboole_0=B_145 | ~v2_funct_1(C_144) | k2_relset_1(A_143, B_145, C_144)!=B_145 | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_143, B_145))) | ~v1_funct_2(C_144, A_143, B_145) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.54/2.56  tff(c_658, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_654])).
% 7.54/2.56  tff(c_666, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_658])).
% 7.54/2.56  tff(c_667, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_666])).
% 7.54/2.56  tff(c_10, plain, (![A_3]: (k2_relat_1(k5_relat_1(A_3, k2_funct_1(A_3)))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.54/2.56  tff(c_675, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_667, c_10])).
% 7.54/2.56  tff(c_682, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_56, c_76, c_675])).
% 7.54/2.56  tff(c_684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_599, c_682])).
% 7.54/2.56  tff(c_686, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_596])).
% 7.54/2.56  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_126, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_113])).
% 7.54/2.56  tff(c_525, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_126, c_522])).
% 7.54/2.56  tff(c_534, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_525])).
% 7.54/2.56  tff(c_535, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_534])).
% 7.54/2.56  tff(c_541, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_535])).
% 7.54/2.56  tff(c_689, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_686, c_541])).
% 7.54/2.56  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_127, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.54/2.56  tff(c_134, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_30, c_127])).
% 7.54/2.56  tff(c_151, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_137])).
% 7.54/2.56  tff(c_1334, plain, (![A_191, B_192, C_193, D_194]: (k2_relset_1(A_191, B_192, C_193)=B_192 | ~r2_relset_1(B_192, B_192, k1_partfun1(B_192, A_191, A_191, B_192, D_194, C_193), k6_partfun1(B_192)) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(B_192, A_191))) | ~v1_funct_2(D_194, B_192, A_191) | ~v1_funct_1(D_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))) | ~v1_funct_2(C_193, A_191, B_192) | ~v1_funct_1(C_193))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.54/2.56  tff(c_1340, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_502, c_1334])).
% 7.54/2.56  tff(c_1344, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_134, c_151, c_1340])).
% 7.54/2.56  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_689, c_1344])).
% 7.54/2.56  tff(c_1347, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_535])).
% 7.54/2.56  tff(c_2460, plain, (![A_312, D_313, F_311, B_309, C_308, E_310]: (k1_partfun1(A_312, B_309, C_308, D_313, E_310, F_311)=k5_relat_1(E_310, F_311) | ~m1_subset_1(F_311, k1_zfmisc_1(k2_zfmisc_1(C_308, D_313))) | ~v1_funct_1(F_311) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(A_312, B_309))) | ~v1_funct_1(E_310))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.54/2.56  tff(c_2466, plain, (![A_312, B_309, E_310]: (k1_partfun1(A_312, B_309, '#skF_2', '#skF_1', E_310, '#skF_4')=k5_relat_1(E_310, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(A_312, B_309))) | ~v1_funct_1(E_310))), inference(resolution, [status(thm)], [c_62, c_2460])).
% 7.54/2.56  tff(c_2479, plain, (![A_315, B_316, E_317]: (k1_partfun1(A_315, B_316, '#skF_2', '#skF_1', E_317, '#skF_4')=k5_relat_1(E_317, '#skF_4') | ~m1_subset_1(E_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))) | ~v1_funct_1(E_317))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2466])).
% 7.54/2.56  tff(c_2485, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2479])).
% 7.54/2.56  tff(c_2492, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_502, c_2485])).
% 7.54/2.56  tff(c_1348, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_535])).
% 7.54/2.56  tff(c_73, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_partfun1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 7.54/2.56  tff(c_1352, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1348, c_73])).
% 7.54/2.56  tff(c_1356, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_66, c_1352])).
% 7.54/2.56  tff(c_1364, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1356])).
% 7.54/2.56  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.54/2.56  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.54/2.56  tff(c_74, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 7.54/2.56  tff(c_2385, plain, (![D_289, B_290, A_287, C_291, E_288]: (k1_xboole_0=C_291 | v2_funct_1(E_288) | k2_relset_1(A_287, B_290, D_289)!=B_290 | ~v2_funct_1(k1_partfun1(A_287, B_290, B_290, C_291, D_289, E_288)) | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(B_290, C_291))) | ~v1_funct_2(E_288, B_290, C_291) | ~v1_funct_1(E_288) | ~m1_subset_1(D_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_290))) | ~v1_funct_2(D_289, A_287, B_290) | ~v1_funct_1(D_289))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.54/2.56  tff(c_2393, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_502, c_2385])).
% 7.54/2.56  tff(c_2404, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_74, c_60, c_2393])).
% 7.54/2.56  tff(c_2406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1364, c_54, c_2404])).
% 7.54/2.56  tff(c_2408, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1356])).
% 7.54/2.56  tff(c_2411, plain, (![A_296, B_297, D_299, E_300, C_295, F_298]: (v1_funct_1(k1_partfun1(A_296, B_297, C_295, D_299, E_300, F_298)) | ~m1_subset_1(F_298, k1_zfmisc_1(k2_zfmisc_1(C_295, D_299))) | ~v1_funct_1(F_298) | ~m1_subset_1(E_300, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))) | ~v1_funct_1(E_300))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.54/2.56  tff(c_2417, plain, (![A_296, B_297, E_300]: (v1_funct_1(k1_partfun1(A_296, B_297, '#skF_2', '#skF_1', E_300, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_300, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))) | ~v1_funct_1(E_300))), inference(resolution, [status(thm)], [c_62, c_2411])).
% 7.54/2.56  tff(c_2443, plain, (![A_305, B_306, E_307]: (v1_funct_1(k1_partfun1(A_305, B_306, '#skF_2', '#skF_1', E_307, '#skF_4')) | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | ~v1_funct_1(E_307))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2417])).
% 7.54/2.56  tff(c_2449, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2443])).
% 7.54/2.56  tff(c_2456, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_502, c_2449])).
% 7.54/2.56  tff(c_2477, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2456, c_540])).
% 7.54/2.56  tff(c_2505, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2477])).
% 7.54/2.56  tff(c_2506, plain, (![A_318, C_319, B_320]: (k6_partfun1(A_318)=k5_relat_1(C_319, k2_funct_1(C_319)) | k1_xboole_0=B_320 | ~v2_funct_1(C_319) | k2_relset_1(A_318, B_320, C_319)!=B_320 | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_318, B_320))) | ~v1_funct_2(C_319, A_318, B_320) | ~v1_funct_1(C_319))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.54/2.56  tff(c_2510, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2506])).
% 7.54/2.56  tff(c_2518, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_2510])).
% 7.54/2.56  tff(c_2519, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_2518])).
% 7.54/2.56  tff(c_2527, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2519, c_10])).
% 7.54/2.56  tff(c_2534, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_72, c_56, c_76, c_2527])).
% 7.54/2.56  tff(c_2536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2505, c_2534])).
% 7.54/2.56  tff(c_2538, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2477])).
% 7.54/2.56  tff(c_1349, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_151])).
% 7.54/2.56  tff(c_2542, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2538, c_1349])).
% 7.54/2.56  tff(c_2588, plain, (![A_324, C_325, B_326]: (k6_partfun1(A_324)=k5_relat_1(C_325, k2_funct_1(C_325)) | k1_xboole_0=B_326 | ~v2_funct_1(C_325) | k2_relset_1(A_324, B_326, C_325)!=B_326 | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_324, B_326))) | ~v1_funct_2(C_325, A_324, B_326) | ~v1_funct_1(C_325))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.54/2.56  tff(c_2594, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2588])).
% 7.54/2.56  tff(c_2604, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2542, c_2408, c_2594])).
% 7.54/2.56  tff(c_2605, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_2604])).
% 7.54/2.56  tff(c_2623, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2605, c_10])).
% 7.54/2.56  tff(c_2630, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_66, c_2408, c_76, c_2623])).
% 7.54/2.56  tff(c_2407, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(splitRight, [status(thm)], [c_1356])).
% 7.54/2.56  tff(c_2539, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k5_relat_1(B_6, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_2538, c_2407])).
% 7.54/2.56  tff(c_4491, plain, (![B_418]: (k2_funct_1('#skF_4')=B_418 | k5_relat_1(B_418, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_418)!='#skF_2' | ~v1_funct_1(B_418) | ~v1_relat_1(B_418))), inference(demodulation, [status(thm), theory('equality')], [c_2630, c_2539])).
% 7.54/2.56  tff(c_4584, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_125, c_4491])).
% 7.54/2.56  tff(c_4676, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_150, c_2492, c_4584])).
% 7.54/2.56  tff(c_4683, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4676, c_2605])).
% 7.54/2.56  tff(c_4686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1347, c_4683])).
% 7.54/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/2.56  
% 7.54/2.56  Inference rules
% 7.54/2.56  ----------------------
% 7.54/2.56  #Ref     : 0
% 7.54/2.56  #Sup     : 958
% 7.54/2.56  #Fact    : 0
% 7.54/2.56  #Define  : 0
% 7.54/2.56  #Split   : 28
% 7.54/2.56  #Chain   : 0
% 7.54/2.56  #Close   : 0
% 7.54/2.56  
% 7.54/2.56  Ordering : KBO
% 7.54/2.56  
% 7.54/2.56  Simplification rules
% 7.54/2.56  ----------------------
% 7.54/2.56  #Subsume      : 38
% 7.54/2.56  #Demod        : 1260
% 7.54/2.56  #Tautology    : 266
% 7.54/2.56  #SimpNegUnit  : 97
% 7.54/2.56  #BackRed      : 49
% 7.54/2.56  
% 7.54/2.56  #Partial instantiations: 0
% 7.54/2.56  #Strategies tried      : 1
% 7.54/2.56  
% 7.54/2.56  Timing (in seconds)
% 7.54/2.56  ----------------------
% 7.54/2.56  Preprocessing        : 0.38
% 7.54/2.57  Parsing              : 0.20
% 7.54/2.57  CNF conversion       : 0.03
% 7.54/2.57  Main loop            : 1.36
% 7.54/2.57  Inferencing          : 0.43
% 7.54/2.57  Reduction            : 0.54
% 7.54/2.57  Demodulation         : 0.41
% 7.54/2.57  BG Simplification    : 0.05
% 7.54/2.57  Subsumption          : 0.25
% 7.54/2.57  Abstraction          : 0.06
% 7.54/2.57  MUC search           : 0.00
% 7.54/2.57  Cooper               : 0.00
% 7.54/2.57  Total                : 1.82
% 7.54/2.57  Index Insertion      : 0.00
% 7.54/2.57  Index Deletion       : 0.00
% 7.54/2.57  Index Matching       : 0.00
% 7.54/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
