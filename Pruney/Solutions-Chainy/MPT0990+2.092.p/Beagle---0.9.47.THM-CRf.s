%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:09 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :  171 (1124 expanded)
%              Number of leaves         :   40 ( 410 expanded)
%              Depth                    :   23
%              Number of atoms          :  429 (4721 expanded)
%              Number of equality atoms :  167 (1698 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

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

tff(c_292,plain,(
    ! [C_85,E_87,F_88,A_89,B_86,D_90] :
      ( k1_partfun1(A_89,B_86,C_85,D_90,E_87,F_88) = k5_relat_1(E_87,F_88)
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_85,D_90)))
      | ~ v1_funct_1(F_88)
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_298,plain,(
    ! [A_89,B_86,E_87] :
      ( k1_partfun1(A_89,B_86,'#skF_2','#skF_1',E_87,'#skF_4') = k5_relat_1(E_87,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_86)))
      | ~ v1_funct_1(E_87) ) ),
    inference(resolution,[status(thm)],[c_62,c_292])).

tff(c_391,plain,(
    ! [A_103,B_104,E_105] :
      ( k1_partfun1(A_103,B_104,'#skF_2','#skF_1',E_105,'#skF_4') = k5_relat_1(E_105,'#skF_4')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_298])).

tff(c_397,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_391])).

tff(c_404,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_397])).

tff(c_30,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_171,plain,(
    ! [D_63,C_64,A_65,B_66] :
      ( D_63 = C_64
      | ~ r2_relset_1(A_65,B_66,C_64,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_177,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_171])).

tff(c_188,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_177])).

tff(c_214,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_409,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_214])).

tff(c_518,plain,(
    ! [B_111,A_110,F_112,C_109,D_113,E_114] :
      ( m1_subset_1(k1_partfun1(A_110,B_111,C_109,D_113,E_114,F_112),k1_zfmisc_1(k2_zfmisc_1(A_110,D_113)))
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_109,D_113)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_549,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_518])).

tff(c_568,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_549])).

tff(c_573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_568])).

tff(c_574,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_619,plain,(
    ! [D_122,A_119,F_121,B_120,E_123,C_118] :
      ( v1_funct_1(k1_partfun1(A_119,B_120,C_118,D_122,E_123,F_121))
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_118,D_122)))
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_625,plain,(
    ! [A_119,B_120,E_123] :
      ( v1_funct_1(k1_partfun1(A_119,B_120,'#skF_2','#skF_1',E_123,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_123) ) ),
    inference(resolution,[status(thm)],[c_62,c_619])).

tff(c_633,plain,(
    ! [A_124,B_125,E_126] :
      ( v1_funct_1(k1_partfun1(A_124,B_125,'#skF_2','#skF_1',E_126,'#skF_4'))
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_1(E_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_625])).

tff(c_639,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_633])).

tff(c_646,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_574,c_639])).

tff(c_34,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_6,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_2] : v1_relat_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_115,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_127,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_115])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_139,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_145,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_139])).

tff(c_152,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_145])).

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

tff(c_583,plain,(
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

tff(c_589,plain,(
    ! [B_116] :
      ( k2_funct_1('#skF_3') = B_116
      | k5_relat_1(B_116,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_116) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_583])).

tff(c_598,plain,(
    ! [B_117] :
      ( k2_funct_1('#skF_3') = B_117
      | k5_relat_1(B_117,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_117) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_56,c_589])).

tff(c_607,plain,(
    ! [A_2] :
      ( k6_partfun1(A_2) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_2),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_2)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_2)) ) ),
    inference(resolution,[status(thm)],[c_77,c_598])).

tff(c_684,plain,(
    ! [A_138] :
      ( k6_partfun1(A_138) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_138),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_138
      | ~ v1_funct_1(k6_partfun1(A_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_607])).

tff(c_688,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_646,c_684])).

tff(c_689,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_688])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_721,plain,(
    ! [A_143,C_144,B_145] :
      ( k6_partfun1(A_143) = k5_relat_1(C_144,k2_funct_1(C_144))
      | k1_xboole_0 = B_145
      | ~ v2_funct_1(C_144)
      | k2_relset_1(A_143,B_145,C_144) != B_145
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_143,B_145)))
      | ~ v1_funct_2(C_144,A_143,B_145)
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_725,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_721])).

tff(c_733,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_725])).

tff(c_734,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_733])).

tff(c_12,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_742,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_74])).

tff(c_749,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_56,c_742])).

tff(c_779,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_79])).

tff(c_803,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_779])).

tff(c_805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_689,c_803])).

tff(c_807,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_688])).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_128,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_115])).

tff(c_601,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_598])).

tff(c_610,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_601])).

tff(c_611,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_610])).

tff(c_617,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_810,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_617])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_129,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_136,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_30,c_129])).

tff(c_153,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_139])).

tff(c_1440,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( k2_relset_1(A_181,B_182,C_183) = B_182
      | ~ r2_relset_1(B_182,B_182,k1_partfun1(B_182,A_181,A_181,B_182,D_184,C_183),k6_partfun1(B_182))
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(B_182,A_181)))
      | ~ v1_funct_2(D_184,B_182,A_181)
      | ~ v1_funct_1(D_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_2(C_183,A_181,B_182)
      | ~ v1_funct_1(C_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1446,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_1440])).

tff(c_1450,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_72,c_70,c_68,c_136,c_153,c_1446])).

tff(c_1452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_810,c_1450])).

tff(c_1453,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_2528,plain,(
    ! [F_286,E_285,D_288,A_287,C_283,B_284] :
      ( k1_partfun1(A_287,B_284,C_283,D_288,E_285,F_286) = k5_relat_1(E_285,F_286)
      | ~ m1_subset_1(F_286,k1_zfmisc_1(k2_zfmisc_1(C_283,D_288)))
      | ~ v1_funct_1(F_286)
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(A_287,B_284)))
      | ~ v1_funct_1(E_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2534,plain,(
    ! [A_287,B_284,E_285] :
      ( k1_partfun1(A_287,B_284,'#skF_2','#skF_1',E_285,'#skF_4') = k5_relat_1(E_285,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(A_287,B_284)))
      | ~ v1_funct_1(E_285) ) ),
    inference(resolution,[status(thm)],[c_62,c_2528])).

tff(c_2547,plain,(
    ! [A_290,B_291,E_292] :
      ( k1_partfun1(A_290,B_291,'#skF_2','#skF_1',E_292,'#skF_4') = k5_relat_1(E_292,'#skF_4')
      | ~ m1_subset_1(E_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | ~ v1_funct_1(E_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2534])).

tff(c_2553,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2547])).

tff(c_2560,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_574,c_2553])).

tff(c_1454,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_611])).

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

tff(c_1458,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_73])).

tff(c_1462,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_66,c_1458])).

tff(c_1470,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1462])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_2441,plain,(
    ! [D_264,C_266,E_263,B_265,A_262] :
      ( k1_xboole_0 = C_266
      | v2_funct_1(E_263)
      | k2_relset_1(A_262,B_265,D_264) != B_265
      | ~ v2_funct_1(k1_partfun1(A_262,B_265,B_265,C_266,D_264,E_263))
      | ~ m1_subset_1(E_263,k1_zfmisc_1(k2_zfmisc_1(B_265,C_266)))
      | ~ v1_funct_2(E_263,B_265,C_266)
      | ~ v1_funct_1(E_263)
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_265)))
      | ~ v1_funct_2(D_264,A_262,B_265)
      | ~ v1_funct_1(D_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2449,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_574,c_2441])).

tff(c_2460,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_62,c_76,c_60,c_2449])).

tff(c_2462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1470,c_54,c_2460])).

tff(c_2464,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1462])).

tff(c_2479,plain,(
    ! [A_271,D_274,F_273,E_275,C_270,B_272] :
      ( v1_funct_1(k1_partfun1(A_271,B_272,C_270,D_274,E_275,F_273))
      | ~ m1_subset_1(F_273,k1_zfmisc_1(k2_zfmisc_1(C_270,D_274)))
      | ~ v1_funct_1(F_273)
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272)))
      | ~ v1_funct_1(E_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2485,plain,(
    ! [A_271,B_272,E_275] :
      ( v1_funct_1(k1_partfun1(A_271,B_272,'#skF_2','#skF_1',E_275,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272)))
      | ~ v1_funct_1(E_275) ) ),
    inference(resolution,[status(thm)],[c_62,c_2479])).

tff(c_2511,plain,(
    ! [A_280,B_281,E_282] :
      ( v1_funct_1(k1_partfun1(A_280,B_281,'#skF_2','#skF_1',E_282,'#skF_4'))
      | ~ m1_subset_1(E_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281)))
      | ~ v1_funct_1(E_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2485])).

tff(c_2517,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2511])).

tff(c_2524,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_574,c_2517])).

tff(c_616,plain,(
    ! [A_2] :
      ( k6_partfun1(A_2) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_2),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_2
      | ~ v1_funct_1(k6_partfun1(A_2)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_607])).

tff(c_2545,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2524,c_616])).

tff(c_2573,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2545])).

tff(c_2574,plain,(
    ! [A_293,C_294,B_295] :
      ( k6_partfun1(A_293) = k5_relat_1(C_294,k2_funct_1(C_294))
      | k1_xboole_0 = B_295
      | ~ v2_funct_1(C_294)
      | k2_relset_1(A_293,B_295,C_294) != B_295
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_293,B_295)))
      | ~ v1_funct_2(C_294,A_293,B_295)
      | ~ v1_funct_1(C_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2578,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2574])).

tff(c_2586,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_2578])).

tff(c_2587,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2586])).

tff(c_2595,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2587,c_74])).

tff(c_2602,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72,c_56,c_2595])).

tff(c_2633,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2602,c_79])).

tff(c_2657,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2633])).

tff(c_2659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2573,c_2657])).

tff(c_2661,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2545])).

tff(c_1455,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1454,c_153])).

tff(c_2665,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_1455])).

tff(c_2706,plain,(
    ! [A_299,C_300,B_301] :
      ( k6_partfun1(A_299) = k5_relat_1(C_300,k2_funct_1(C_300))
      | k1_xboole_0 = B_301
      | ~ v2_funct_1(C_300)
      | k2_relset_1(A_299,B_301,C_300) != B_301
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_299,B_301)))
      | ~ v1_funct_2(C_300,A_299,B_301)
      | ~ v1_funct_1(C_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2712,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2706])).

tff(c_2722,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2665,c_2464,c_2712])).

tff(c_2723,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2722])).

tff(c_2741,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2723,c_74])).

tff(c_2748,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_66,c_2464,c_2741])).

tff(c_2775,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2748,c_79])).

tff(c_2793,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2775])).

tff(c_2463,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_6,'#skF_4')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(splitRight,[status(thm)],[c_1462])).

tff(c_2662,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_4') = B_6
      | k5_relat_1(B_6,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_6) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_2463])).

tff(c_5028,plain,(
    ! [B_407] :
      ( k2_funct_1('#skF_4') = B_407
      | k5_relat_1(B_407,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_407) != '#skF_2'
      | ~ v1_funct_1(B_407)
      | ~ v1_relat_1(B_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2793,c_2662])).

tff(c_5121,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_5028])).

tff(c_5213,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_152,c_2560,c_5121])).

tff(c_5218,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5213,c_2723])).

tff(c_5221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1453,c_5218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.65  
% 7.08/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.66  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.08/2.66  
% 7.08/2.66  %Foreground sorts:
% 7.08/2.66  
% 7.08/2.66  
% 7.08/2.66  %Background operators:
% 7.08/2.66  
% 7.08/2.66  
% 7.08/2.66  %Foreground operators:
% 7.08/2.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.08/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.08/2.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.08/2.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.08/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.08/2.66  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.08/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.08/2.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.08/2.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.08/2.66  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.08/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.08/2.66  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.08/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.08/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.08/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.08/2.66  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.08/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.08/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.08/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.08/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.08/2.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.08/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.08/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.08/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.08/2.66  
% 7.27/2.69  tff(f_189, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.27/2.69  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.27/2.69  tff(f_92, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.27/2.69  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.27/2.69  tff(f_88, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.27/2.69  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.27/2.69  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.27/2.69  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.27/2.69  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.27/2.69  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.27/2.69  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 7.27/2.69  tff(f_163, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.27/2.69  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.27/2.69  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.27/2.69  tff(f_147, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.27/2.69  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_292, plain, (![C_85, E_87, F_88, A_89, B_86, D_90]: (k1_partfun1(A_89, B_86, C_85, D_90, E_87, F_88)=k5_relat_1(E_87, F_88) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_85, D_90))) | ~v1_funct_1(F_88) | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_86))) | ~v1_funct_1(E_87))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.27/2.69  tff(c_298, plain, (![A_89, B_86, E_87]: (k1_partfun1(A_89, B_86, '#skF_2', '#skF_1', E_87, '#skF_4')=k5_relat_1(E_87, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_86))) | ~v1_funct_1(E_87))), inference(resolution, [status(thm)], [c_62, c_292])).
% 7.27/2.69  tff(c_391, plain, (![A_103, B_104, E_105]: (k1_partfun1(A_103, B_104, '#skF_2', '#skF_1', E_105, '#skF_4')=k5_relat_1(E_105, '#skF_4') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(E_105))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_298])).
% 7.27/2.69  tff(c_397, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_391])).
% 7.27/2.69  tff(c_404, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_397])).
% 7.27/2.69  tff(c_30, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.27/2.69  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_171, plain, (![D_63, C_64, A_65, B_66]: (D_63=C_64 | ~r2_relset_1(A_65, B_66, C_64, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.27/2.69  tff(c_177, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_171])).
% 7.27/2.69  tff(c_188, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_177])).
% 7.27/2.69  tff(c_214, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_188])).
% 7.27/2.69  tff(c_409, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_214])).
% 7.27/2.69  tff(c_518, plain, (![B_111, A_110, F_112, C_109, D_113, E_114]: (m1_subset_1(k1_partfun1(A_110, B_111, C_109, D_113, E_114, F_112), k1_zfmisc_1(k2_zfmisc_1(A_110, D_113))) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_109, D_113))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.27/2.69  tff(c_549, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_404, c_518])).
% 7.27/2.69  tff(c_568, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_549])).
% 7.27/2.69  tff(c_573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_409, c_568])).
% 7.27/2.69  tff(c_574, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_188])).
% 7.27/2.69  tff(c_619, plain, (![D_122, A_119, F_121, B_120, E_123, C_118]: (v1_funct_1(k1_partfun1(A_119, B_120, C_118, D_122, E_123, F_121)) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_118, D_122))) | ~v1_funct_1(F_121) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_123))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.27/2.69  tff(c_625, plain, (![A_119, B_120, E_123]: (v1_funct_1(k1_partfun1(A_119, B_120, '#skF_2', '#skF_1', E_123, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_123))), inference(resolution, [status(thm)], [c_62, c_619])).
% 7.27/2.69  tff(c_633, plain, (![A_124, B_125, E_126]: (v1_funct_1(k1_partfun1(A_124, B_125, '#skF_2', '#skF_1', E_126, '#skF_4')) | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_1(E_126))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_625])).
% 7.27/2.69  tff(c_639, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_633])).
% 7.27/2.69  tff(c_646, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_574, c_639])).
% 7.27/2.69  tff(c_34, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.27/2.69  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.27/2.69  tff(c_78, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4])).
% 7.27/2.69  tff(c_6, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.27/2.69  tff(c_77, plain, (![A_2]: (v1_relat_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 7.27/2.69  tff(c_115, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.27/2.69  tff(c_127, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_115])).
% 7.27/2.69  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_139, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.27/2.69  tff(c_145, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_139])).
% 7.27/2.69  tff(c_152, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_145])).
% 7.27/2.69  tff(c_14, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.27/2.69  tff(c_583, plain, (![A_115, B_116]: (k2_funct_1(A_115)=B_116 | k6_partfun1(k2_relat_1(A_115))!=k5_relat_1(B_116, A_115) | k2_relat_1(B_116)!=k1_relat_1(A_115) | ~v2_funct_1(A_115) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 7.27/2.69  tff(c_589, plain, (![B_116]: (k2_funct_1('#skF_3')=B_116 | k5_relat_1(B_116, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_116)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_583])).
% 7.27/2.69  tff(c_598, plain, (![B_117]: (k2_funct_1('#skF_3')=B_117 | k5_relat_1(B_117, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_117)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_117) | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_56, c_589])).
% 7.27/2.69  tff(c_607, plain, (![A_2]: (k6_partfun1(A_2)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_2), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_2))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_2)))), inference(resolution, [status(thm)], [c_77, c_598])).
% 7.27/2.69  tff(c_684, plain, (![A_138]: (k6_partfun1(A_138)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_138), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_138 | ~v1_funct_1(k6_partfun1(A_138)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_607])).
% 7.27/2.69  tff(c_688, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_646, c_684])).
% 7.27/2.69  tff(c_689, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_688])).
% 7.27/2.69  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.27/2.69  tff(c_79, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2])).
% 7.27/2.69  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_721, plain, (![A_143, C_144, B_145]: (k6_partfun1(A_143)=k5_relat_1(C_144, k2_funct_1(C_144)) | k1_xboole_0=B_145 | ~v2_funct_1(C_144) | k2_relset_1(A_143, B_145, C_144)!=B_145 | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_143, B_145))) | ~v1_funct_2(C_144, A_143, B_145) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.27/2.69  tff(c_725, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_721])).
% 7.27/2.69  tff(c_733, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_725])).
% 7.27/2.69  tff(c_734, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_733])).
% 7.27/2.69  tff(c_12, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.27/2.69  tff(c_74, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 7.27/2.69  tff(c_742, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_734, c_74])).
% 7.27/2.69  tff(c_749, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_56, c_742])).
% 7.27/2.69  tff(c_779, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_749, c_79])).
% 7.27/2.69  tff(c_803, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_779])).
% 7.27/2.69  tff(c_805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_689, c_803])).
% 7.27/2.69  tff(c_807, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_688])).
% 7.27/2.69  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_128, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_115])).
% 7.27/2.69  tff(c_601, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_598])).
% 7.27/2.69  tff(c_610, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_601])).
% 7.27/2.69  tff(c_611, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_610])).
% 7.27/2.69  tff(c_617, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_611])).
% 7.27/2.69  tff(c_810, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_807, c_617])).
% 7.27/2.69  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_129, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.27/2.69  tff(c_136, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_30, c_129])).
% 7.27/2.69  tff(c_153, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_139])).
% 7.27/2.69  tff(c_1440, plain, (![A_181, B_182, C_183, D_184]: (k2_relset_1(A_181, B_182, C_183)=B_182 | ~r2_relset_1(B_182, B_182, k1_partfun1(B_182, A_181, A_181, B_182, D_184, C_183), k6_partfun1(B_182)) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(B_182, A_181))) | ~v1_funct_2(D_184, B_182, A_181) | ~v1_funct_1(D_184) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_2(C_183, A_181, B_182) | ~v1_funct_1(C_183))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.27/2.69  tff(c_1446, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_574, c_1440])).
% 7.27/2.69  tff(c_1450, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_72, c_70, c_68, c_136, c_153, c_1446])).
% 7.27/2.69  tff(c_1452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_810, c_1450])).
% 7.27/2.69  tff(c_1453, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_611])).
% 7.27/2.69  tff(c_2528, plain, (![F_286, E_285, D_288, A_287, C_283, B_284]: (k1_partfun1(A_287, B_284, C_283, D_288, E_285, F_286)=k5_relat_1(E_285, F_286) | ~m1_subset_1(F_286, k1_zfmisc_1(k2_zfmisc_1(C_283, D_288))) | ~v1_funct_1(F_286) | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(A_287, B_284))) | ~v1_funct_1(E_285))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.27/2.69  tff(c_2534, plain, (![A_287, B_284, E_285]: (k1_partfun1(A_287, B_284, '#skF_2', '#skF_1', E_285, '#skF_4')=k5_relat_1(E_285, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(A_287, B_284))) | ~v1_funct_1(E_285))), inference(resolution, [status(thm)], [c_62, c_2528])).
% 7.27/2.69  tff(c_2547, plain, (![A_290, B_291, E_292]: (k1_partfun1(A_290, B_291, '#skF_2', '#skF_1', E_292, '#skF_4')=k5_relat_1(E_292, '#skF_4') | ~m1_subset_1(E_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | ~v1_funct_1(E_292))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2534])).
% 7.27/2.69  tff(c_2553, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2547])).
% 7.27/2.69  tff(c_2560, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_574, c_2553])).
% 7.27/2.69  tff(c_1454, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_611])).
% 7.27/2.69  tff(c_73, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_partfun1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 7.27/2.69  tff(c_1458, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1454, c_73])).
% 7.27/2.69  tff(c_1462, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_66, c_1458])).
% 7.27/2.69  tff(c_1470, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1462])).
% 7.27/2.69  tff(c_54, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.27/2.69  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.27/2.69  tff(c_76, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 7.27/2.69  tff(c_2441, plain, (![D_264, C_266, E_263, B_265, A_262]: (k1_xboole_0=C_266 | v2_funct_1(E_263) | k2_relset_1(A_262, B_265, D_264)!=B_265 | ~v2_funct_1(k1_partfun1(A_262, B_265, B_265, C_266, D_264, E_263)) | ~m1_subset_1(E_263, k1_zfmisc_1(k2_zfmisc_1(B_265, C_266))) | ~v1_funct_2(E_263, B_265, C_266) | ~v1_funct_1(E_263) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_265))) | ~v1_funct_2(D_264, A_262, B_265) | ~v1_funct_1(D_264))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.27/2.69  tff(c_2449, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_574, c_2441])).
% 7.27/2.69  tff(c_2460, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_62, c_76, c_60, c_2449])).
% 7.27/2.69  tff(c_2462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1470, c_54, c_2460])).
% 7.27/2.69  tff(c_2464, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1462])).
% 7.27/2.69  tff(c_2479, plain, (![A_271, D_274, F_273, E_275, C_270, B_272]: (v1_funct_1(k1_partfun1(A_271, B_272, C_270, D_274, E_275, F_273)) | ~m1_subset_1(F_273, k1_zfmisc_1(k2_zfmisc_1(C_270, D_274))) | ~v1_funct_1(F_273) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))) | ~v1_funct_1(E_275))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.27/2.69  tff(c_2485, plain, (![A_271, B_272, E_275]: (v1_funct_1(k1_partfun1(A_271, B_272, '#skF_2', '#skF_1', E_275, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))) | ~v1_funct_1(E_275))), inference(resolution, [status(thm)], [c_62, c_2479])).
% 7.27/2.69  tff(c_2511, plain, (![A_280, B_281, E_282]: (v1_funct_1(k1_partfun1(A_280, B_281, '#skF_2', '#skF_1', E_282, '#skF_4')) | ~m1_subset_1(E_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))) | ~v1_funct_1(E_282))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2485])).
% 7.27/2.69  tff(c_2517, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2511])).
% 7.27/2.69  tff(c_2524, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_574, c_2517])).
% 7.27/2.69  tff(c_616, plain, (![A_2]: (k6_partfun1(A_2)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_2), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_2 | ~v1_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_607])).
% 7.27/2.69  tff(c_2545, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2524, c_616])).
% 7.27/2.69  tff(c_2573, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2545])).
% 7.27/2.69  tff(c_2574, plain, (![A_293, C_294, B_295]: (k6_partfun1(A_293)=k5_relat_1(C_294, k2_funct_1(C_294)) | k1_xboole_0=B_295 | ~v2_funct_1(C_294) | k2_relset_1(A_293, B_295, C_294)!=B_295 | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_293, B_295))) | ~v1_funct_2(C_294, A_293, B_295) | ~v1_funct_1(C_294))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.27/2.69  tff(c_2578, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2574])).
% 7.27/2.69  tff(c_2586, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_2578])).
% 7.27/2.69  tff(c_2587, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_2586])).
% 7.27/2.69  tff(c_2595, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2587, c_74])).
% 7.27/2.69  tff(c_2602, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72, c_56, c_2595])).
% 7.27/2.69  tff(c_2633, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2602, c_79])).
% 7.27/2.69  tff(c_2657, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_2633])).
% 7.27/2.69  tff(c_2659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2573, c_2657])).
% 7.27/2.69  tff(c_2661, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2545])).
% 7.27/2.69  tff(c_1455, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1454, c_153])).
% 7.27/2.69  tff(c_2665, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_1455])).
% 7.27/2.69  tff(c_2706, plain, (![A_299, C_300, B_301]: (k6_partfun1(A_299)=k5_relat_1(C_300, k2_funct_1(C_300)) | k1_xboole_0=B_301 | ~v2_funct_1(C_300) | k2_relset_1(A_299, B_301, C_300)!=B_301 | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_299, B_301))) | ~v1_funct_2(C_300, A_299, B_301) | ~v1_funct_1(C_300))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.27/2.69  tff(c_2712, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2706])).
% 7.27/2.69  tff(c_2722, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2665, c_2464, c_2712])).
% 7.27/2.69  tff(c_2723, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_2722])).
% 7.27/2.69  tff(c_2741, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2723, c_74])).
% 7.27/2.69  tff(c_2748, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_66, c_2464, c_2741])).
% 7.27/2.69  tff(c_2775, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2748, c_79])).
% 7.27/2.69  tff(c_2793, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_2775])).
% 7.27/2.69  tff(c_2463, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_6, '#skF_4') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(splitRight, [status(thm)], [c_1462])).
% 7.27/2.69  tff(c_2662, plain, (![B_6]: (k2_funct_1('#skF_4')=B_6 | k5_relat_1(B_6, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_6)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_2463])).
% 7.27/2.69  tff(c_5028, plain, (![B_407]: (k2_funct_1('#skF_4')=B_407 | k5_relat_1(B_407, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_407)!='#skF_2' | ~v1_funct_1(B_407) | ~v1_relat_1(B_407))), inference(demodulation, [status(thm), theory('equality')], [c_2793, c_2662])).
% 7.27/2.69  tff(c_5121, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_127, c_5028])).
% 7.27/2.69  tff(c_5213, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_152, c_2560, c_5121])).
% 7.27/2.69  tff(c_5218, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5213, c_2723])).
% 7.27/2.69  tff(c_5221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1453, c_5218])).
% 7.27/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.27/2.69  
% 7.27/2.69  Inference rules
% 7.27/2.69  ----------------------
% 7.27/2.69  #Ref     : 0
% 7.27/2.69  #Sup     : 1082
% 7.27/2.69  #Fact    : 0
% 7.27/2.69  #Define  : 0
% 7.27/2.69  #Split   : 31
% 7.27/2.69  #Chain   : 0
% 7.27/2.69  #Close   : 0
% 7.27/2.69  
% 7.27/2.69  Ordering : KBO
% 7.27/2.69  
% 7.27/2.69  Simplification rules
% 7.27/2.69  ----------------------
% 7.27/2.69  #Subsume      : 68
% 7.27/2.69  #Demod        : 1826
% 7.27/2.69  #Tautology    : 307
% 7.27/2.69  #SimpNegUnit  : 124
% 7.27/2.69  #BackRed      : 50
% 7.27/2.69  
% 7.27/2.69  #Partial instantiations: 0
% 7.27/2.69  #Strategies tried      : 1
% 7.27/2.69  
% 7.27/2.69  Timing (in seconds)
% 7.27/2.69  ----------------------
% 7.27/2.69  Preprocessing        : 0.37
% 7.27/2.69  Parsing              : 0.20
% 7.27/2.69  CNF conversion       : 0.02
% 7.27/2.69  Main loop            : 1.51
% 7.27/2.69  Inferencing          : 0.44
% 7.27/2.69  Reduction            : 0.66
% 7.27/2.69  Demodulation         : 0.50
% 7.27/2.69  BG Simplification    : 0.05
% 7.27/2.69  Subsumption          : 0.26
% 7.27/2.69  Abstraction          : 0.06
% 7.27/2.69  MUC search           : 0.00
% 7.27/2.69  Cooper               : 0.00
% 7.27/2.69  Total                : 1.94
% 7.27/2.69  Index Insertion      : 0.00
% 7.27/2.69  Index Deletion       : 0.00
% 7.27/2.69  Index Matching       : 0.00
% 7.27/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
