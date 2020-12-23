%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:23 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 579 expanded)
%              Number of leaves         :   44 ( 220 expanded)
%              Depth                    :   15
%              Number of atoms          :  317 (2380 expanded)
%              Number of equality atoms :   90 ( 817 expanded)
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

tff(f_207,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_181,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_139,axiom,(
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

tff(f_122,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_165,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_58,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_105,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_105])).

tff(c_123,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_114])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_206,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_219,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_206])).

tff(c_1984,plain,(
    ! [A_171,C_172,B_173] :
      ( k6_partfun1(A_171) = k5_relat_1(C_172,k2_funct_1(C_172))
      | k1_xboole_0 = B_173
      | ~ v2_funct_1(C_172)
      | k2_relset_1(A_171,B_173,C_172) != B_173
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_171,B_173)))
      | ~ v1_funct_2(C_172,A_171,B_173)
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1990,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1984])).

tff(c_2000,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_219,c_1990])).

tff(c_2001,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2000])).

tff(c_2024,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2001])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_38,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_165,plain,(
    ! [A_69,B_70,D_71] :
      ( r2_relset_1(A_69,B_70,D_71,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_172,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_38,c_165])).

tff(c_906,plain,(
    ! [E_108,D_111,C_109,F_110,A_107,B_112] :
      ( k1_partfun1(A_107,B_112,C_109,D_111,E_108,F_110) = k5_relat_1(E_108,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_109,D_111)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_107,B_112)))
      | ~ v1_funct_1(E_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_912,plain,(
    ! [A_107,B_112,E_108] :
      ( k1_partfun1(A_107,B_112,'#skF_2','#skF_1',E_108,'#skF_4') = k5_relat_1(E_108,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_107,B_112)))
      | ~ v1_funct_1(E_108) ) ),
    inference(resolution,[status(thm)],[c_70,c_906])).

tff(c_1228,plain,(
    ! [A_129,B_130,E_131] :
      ( k1_partfun1(A_129,B_130,'#skF_2','#skF_1',E_131,'#skF_4') = k5_relat_1(E_131,'#skF_4')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_912])).

tff(c_1234,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1228])).

tff(c_1241,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1234])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_498,plain,(
    ! [D_88,C_89,A_90,B_91] :
      ( D_88 = C_89
      | ~ r2_relset_1(A_90,B_91,C_89,D_88)
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_506,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_498])).

tff(c_521,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_506])).

tff(c_538,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_1246,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_538])).

tff(c_1418,plain,(
    ! [E_140,F_138,B_136,A_137,C_139,D_135] :
      ( m1_subset_1(k1_partfun1(A_137,B_136,C_139,D_135,E_140,F_138),k1_zfmisc_1(k2_zfmisc_1(A_137,D_135)))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(C_139,D_135)))
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1452,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_1418])).

tff(c_1475,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1452])).

tff(c_1477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1246,c_1475])).

tff(c_1478,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_2755,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( k2_relset_1(A_201,B_202,C_203) = B_202
      | ~ r2_relset_1(B_202,B_202,k1_partfun1(B_202,A_201,A_201,B_202,D_204,C_203),k6_partfun1(B_202))
      | ~ m1_subset_1(D_204,k1_zfmisc_1(k2_zfmisc_1(B_202,A_201)))
      | ~ v1_funct_2(D_204,B_202,A_201)
      | ~ v1_funct_1(D_204)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_2(C_203,A_201,B_202)
      | ~ v1_funct_1(C_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2761,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_2755])).

tff(c_2765,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_172,c_219,c_2761])).

tff(c_2767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2024,c_2765])).

tff(c_2768,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2001])).

tff(c_2808,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2768])).

tff(c_42,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_18,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_3290,plain,(
    ! [E_227,D_228,B_225,C_229,A_226] :
      ( k1_xboole_0 = C_229
      | v2_funct_1(E_227)
      | k2_relset_1(A_226,B_225,D_228) != B_225
      | ~ v2_funct_1(k1_partfun1(A_226,B_225,B_225,C_229,D_228,E_227))
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(B_225,C_229)))
      | ~ v1_funct_2(E_227,B_225,C_229)
      | ~ v1_funct_1(E_227)
      | ~ m1_subset_1(D_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225)))
      | ~ v1_funct_2(D_228,A_226,B_225)
      | ~ v1_funct_1(D_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3294,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_3290])).

tff(c_3299,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_81,c_68,c_3294])).

tff(c_3301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2808,c_62,c_3299])).

tff(c_3303,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2768])).

tff(c_14,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3302,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2768])).

tff(c_16,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_82,plain,(
    ! [A_16] : v1_relat_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_8,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_13)),A_13) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_13)),A_13) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_233,plain,(
    ! [A_78,B_79,C_80] :
      ( k5_relat_1(k5_relat_1(A_78,B_79),C_80) = k5_relat_1(A_78,k5_relat_1(B_79,C_80))
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_255,plain,(
    ! [A_13,C_80] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_13)),k5_relat_1(A_13,C_80)) = k5_relat_1(A_13,C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_233])).

tff(c_270,plain,(
    ! [A_13,C_80] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_13)),k5_relat_1(A_13,C_80)) = k5_relat_1(A_13,C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_255])).

tff(c_3307,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3302,c_270])).

tff(c_3314,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_3302,c_3307])).

tff(c_3530,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3314])).

tff(c_3595,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_3530])).

tff(c_3599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_74,c_3595])).

tff(c_3601,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3314])).

tff(c_111,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_105])).

tff(c_120,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_111])).

tff(c_212,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_206])).

tff(c_218,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_212])).

tff(c_10,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_83,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_partfun1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_223,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_83])).

tff(c_227,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_223])).

tff(c_2769,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2001])).

tff(c_191,plain,(
    ! [A_74] :
      ( k1_relat_1(k2_funct_1(A_74)) = k2_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4757,plain,(
    ! [A_274] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_274)),k2_funct_1(A_274)) = k2_funct_1(A_274)
      | ~ v1_relat_1(k2_funct_1(A_274))
      | ~ v2_funct_1(A_274)
      | ~ v1_funct_1(A_274)
      | ~ v1_relat_1(A_274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_84])).

tff(c_4783,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2769,c_4757])).

tff(c_4807,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_74,c_3303,c_3601,c_4783])).

tff(c_1938,plain,(
    ! [F_163,C_162,A_160,B_165,D_164,E_161] :
      ( k1_partfun1(A_160,B_165,C_162,D_164,E_161,F_163) = k5_relat_1(E_161,F_163)
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(C_162,D_164)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_165)))
      | ~ v1_funct_1(E_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1944,plain,(
    ! [A_160,B_165,E_161] :
      ( k1_partfun1(A_160,B_165,'#skF_2','#skF_1',E_161,'#skF_4') = k5_relat_1(E_161,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_165)))
      | ~ v1_funct_1(E_161) ) ),
    inference(resolution,[status(thm)],[c_70,c_1938])).

tff(c_3354,plain,(
    ! [A_230,B_231,E_232] :
      ( k1_partfun1(A_230,B_231,'#skF_2','#skF_1',E_232,'#skF_4') = k5_relat_1(E_232,'#skF_4')
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231)))
      | ~ v1_funct_1(E_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1944])).

tff(c_3360,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3354])).

tff(c_3367,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1478,c_3360])).

tff(c_6,plain,(
    ! [A_6,B_10,C_12] :
      ( k5_relat_1(k5_relat_1(A_6,B_10),C_12) = k5_relat_1(A_6,k5_relat_1(B_10,C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3383,plain,(
    ! [C_12] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_12) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3367,c_6])).

tff(c_3393,plain,(
    ! [C_12] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_12) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_12))
      | ~ v1_relat_1(C_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_123,c_3383])).

tff(c_4813,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4807,c_3393])).

tff(c_4829,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3601,c_227,c_3302,c_4813])).

tff(c_24,plain,(
    ! [A_18] :
      ( k2_funct_1(k2_funct_1(A_18)) = A_18
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4864,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4829,c_24])).

tff(c_4882,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_74,c_3303,c_4864])).

tff(c_4884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.15/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.41  
% 7.15/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.42  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.15/2.42  
% 7.15/2.42  %Foreground sorts:
% 7.15/2.42  
% 7.15/2.42  
% 7.15/2.42  %Background operators:
% 7.15/2.42  
% 7.15/2.42  
% 7.15/2.42  %Foreground operators:
% 7.15/2.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.15/2.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.15/2.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.15/2.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.15/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.15/2.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.15/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.15/2.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.15/2.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.15/2.42  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.15/2.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.15/2.42  tff('#skF_2', type, '#skF_2': $i).
% 7.15/2.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.15/2.42  tff('#skF_3', type, '#skF_3': $i).
% 7.15/2.42  tff('#skF_1', type, '#skF_1': $i).
% 7.15/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.15/2.42  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.15/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.15/2.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.15/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.15/2.42  tff('#skF_4', type, '#skF_4': $i).
% 7.15/2.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.15/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.15/2.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.15/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.15/2.42  
% 7.15/2.44  tff(f_207, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.15/2.44  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.15/2.44  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.15/2.44  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.15/2.44  tff(f_181, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.15/2.44  tff(f_110, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.15/2.44  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.15/2.44  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.15/2.44  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.15/2.44  tff(f_139, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.15/2.44  tff(f_122, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.15/2.44  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.15/2.44  tff(f_165, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.15/2.44  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.15/2.44  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 7.15/2.44  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.15/2.44  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 7.15/2.44  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.15/2.44  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 7.15/2.44  tff(c_58, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.15/2.44  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_105, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.15/2.44  tff(c_114, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_105])).
% 7.15/2.44  tff(c_123, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_114])).
% 7.15/2.44  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_62, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_206, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.15/2.44  tff(c_219, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_206])).
% 7.15/2.44  tff(c_1984, plain, (![A_171, C_172, B_173]: (k6_partfun1(A_171)=k5_relat_1(C_172, k2_funct_1(C_172)) | k1_xboole_0=B_173 | ~v2_funct_1(C_172) | k2_relset_1(A_171, B_173, C_172)!=B_173 | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_171, B_173))) | ~v1_funct_2(C_172, A_171, B_173) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_181])).
% 7.15/2.44  tff(c_1990, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_1984])).
% 7.15/2.44  tff(c_2000, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_219, c_1990])).
% 7.15/2.44  tff(c_2001, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_2000])).
% 7.15/2.44  tff(c_2024, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2001])).
% 7.15/2.44  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_38, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.15/2.44  tff(c_165, plain, (![A_69, B_70, D_71]: (r2_relset_1(A_69, B_70, D_71, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.15/2.44  tff(c_172, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_38, c_165])).
% 7.15/2.44  tff(c_906, plain, (![E_108, D_111, C_109, F_110, A_107, B_112]: (k1_partfun1(A_107, B_112, C_109, D_111, E_108, F_110)=k5_relat_1(E_108, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_109, D_111))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_107, B_112))) | ~v1_funct_1(E_108))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.15/2.44  tff(c_912, plain, (![A_107, B_112, E_108]: (k1_partfun1(A_107, B_112, '#skF_2', '#skF_1', E_108, '#skF_4')=k5_relat_1(E_108, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_107, B_112))) | ~v1_funct_1(E_108))), inference(resolution, [status(thm)], [c_70, c_906])).
% 7.15/2.44  tff(c_1228, plain, (![A_129, B_130, E_131]: (k1_partfun1(A_129, B_130, '#skF_2', '#skF_1', E_131, '#skF_4')=k5_relat_1(E_131, '#skF_4') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_131))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_912])).
% 7.15/2.44  tff(c_1234, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1228])).
% 7.15/2.44  tff(c_1241, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1234])).
% 7.15/2.44  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_498, plain, (![D_88, C_89, A_90, B_91]: (D_88=C_89 | ~r2_relset_1(A_90, B_91, C_89, D_88) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.15/2.44  tff(c_506, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_498])).
% 7.15/2.44  tff(c_521, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_506])).
% 7.15/2.44  tff(c_538, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_521])).
% 7.15/2.44  tff(c_1246, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_538])).
% 7.15/2.44  tff(c_1418, plain, (![E_140, F_138, B_136, A_137, C_139, D_135]: (m1_subset_1(k1_partfun1(A_137, B_136, C_139, D_135, E_140, F_138), k1_zfmisc_1(k2_zfmisc_1(A_137, D_135))) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(C_139, D_135))) | ~v1_funct_1(F_138) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.15/2.44  tff(c_1452, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1241, c_1418])).
% 7.15/2.44  tff(c_1475, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1452])).
% 7.15/2.44  tff(c_1477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1246, c_1475])).
% 7.15/2.44  tff(c_1478, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_521])).
% 7.15/2.44  tff(c_2755, plain, (![A_201, B_202, C_203, D_204]: (k2_relset_1(A_201, B_202, C_203)=B_202 | ~r2_relset_1(B_202, B_202, k1_partfun1(B_202, A_201, A_201, B_202, D_204, C_203), k6_partfun1(B_202)) | ~m1_subset_1(D_204, k1_zfmisc_1(k2_zfmisc_1(B_202, A_201))) | ~v1_funct_2(D_204, B_202, A_201) | ~v1_funct_1(D_204) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~v1_funct_2(C_203, A_201, B_202) | ~v1_funct_1(C_203))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.15/2.44  tff(c_2761, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1478, c_2755])).
% 7.15/2.44  tff(c_2765, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_172, c_219, c_2761])).
% 7.15/2.44  tff(c_2767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2024, c_2765])).
% 7.15/2.44  tff(c_2768, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2001])).
% 7.15/2.44  tff(c_2808, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2768])).
% 7.15/2.44  tff(c_42, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.15/2.44  tff(c_18, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.15/2.44  tff(c_81, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 7.15/2.44  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_207])).
% 7.15/2.44  tff(c_3290, plain, (![E_227, D_228, B_225, C_229, A_226]: (k1_xboole_0=C_229 | v2_funct_1(E_227) | k2_relset_1(A_226, B_225, D_228)!=B_225 | ~v2_funct_1(k1_partfun1(A_226, B_225, B_225, C_229, D_228, E_227)) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(B_225, C_229))) | ~v1_funct_2(E_227, B_225, C_229) | ~v1_funct_1(E_227) | ~m1_subset_1(D_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))) | ~v1_funct_2(D_228, A_226, B_225) | ~v1_funct_1(D_228))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.15/2.44  tff(c_3294, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1478, c_3290])).
% 7.15/2.44  tff(c_3299, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_81, c_68, c_3294])).
% 7.15/2.44  tff(c_3301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2808, c_62, c_3299])).
% 7.15/2.44  tff(c_3303, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2768])).
% 7.15/2.44  tff(c_14, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.15/2.44  tff(c_3302, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2768])).
% 7.15/2.44  tff(c_16, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.15/2.44  tff(c_82, plain, (![A_16]: (v1_relat_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 7.15/2.44  tff(c_8, plain, (![A_13]: (k5_relat_1(k6_relat_1(k1_relat_1(A_13)), A_13)=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.15/2.44  tff(c_84, plain, (![A_13]: (k5_relat_1(k6_partfun1(k1_relat_1(A_13)), A_13)=A_13 | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 7.15/2.44  tff(c_233, plain, (![A_78, B_79, C_80]: (k5_relat_1(k5_relat_1(A_78, B_79), C_80)=k5_relat_1(A_78, k5_relat_1(B_79, C_80)) | ~v1_relat_1(C_80) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.15/2.44  tff(c_255, plain, (![A_13, C_80]: (k5_relat_1(k6_partfun1(k1_relat_1(A_13)), k5_relat_1(A_13, C_80))=k5_relat_1(A_13, C_80) | ~v1_relat_1(C_80) | ~v1_relat_1(A_13) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_84, c_233])).
% 7.15/2.44  tff(c_270, plain, (![A_13, C_80]: (k5_relat_1(k6_partfun1(k1_relat_1(A_13)), k5_relat_1(A_13, C_80))=k5_relat_1(A_13, C_80) | ~v1_relat_1(C_80) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_255])).
% 7.15/2.44  tff(c_3307, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3302, c_270])).
% 7.15/2.44  tff(c_3314, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_3302, c_3307])).
% 7.15/2.44  tff(c_3530, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3314])).
% 7.15/2.44  tff(c_3595, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_3530])).
% 7.15/2.44  tff(c_3599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_74, c_3595])).
% 7.15/2.44  tff(c_3601, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3314])).
% 7.15/2.44  tff(c_111, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_105])).
% 7.15/2.44  tff(c_120, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_111])).
% 7.15/2.44  tff(c_212, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_206])).
% 7.15/2.44  tff(c_218, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_212])).
% 7.15/2.44  tff(c_10, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.15/2.44  tff(c_83, plain, (![A_14]: (k5_relat_1(A_14, k6_partfun1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 7.15/2.44  tff(c_223, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_218, c_83])).
% 7.15/2.44  tff(c_227, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_223])).
% 7.15/2.44  tff(c_2769, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2001])).
% 7.15/2.44  tff(c_191, plain, (![A_74]: (k1_relat_1(k2_funct_1(A_74))=k2_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.15/2.44  tff(c_4757, plain, (![A_274]: (k5_relat_1(k6_partfun1(k2_relat_1(A_274)), k2_funct_1(A_274))=k2_funct_1(A_274) | ~v1_relat_1(k2_funct_1(A_274)) | ~v2_funct_1(A_274) | ~v1_funct_1(A_274) | ~v1_relat_1(A_274))), inference(superposition, [status(thm), theory('equality')], [c_191, c_84])).
% 7.15/2.44  tff(c_4783, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2769, c_4757])).
% 7.15/2.44  tff(c_4807, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_74, c_3303, c_3601, c_4783])).
% 7.15/2.44  tff(c_1938, plain, (![F_163, C_162, A_160, B_165, D_164, E_161]: (k1_partfun1(A_160, B_165, C_162, D_164, E_161, F_163)=k5_relat_1(E_161, F_163) | ~m1_subset_1(F_163, k1_zfmisc_1(k2_zfmisc_1(C_162, D_164))) | ~v1_funct_1(F_163) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_165))) | ~v1_funct_1(E_161))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.15/2.44  tff(c_1944, plain, (![A_160, B_165, E_161]: (k1_partfun1(A_160, B_165, '#skF_2', '#skF_1', E_161, '#skF_4')=k5_relat_1(E_161, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_165))) | ~v1_funct_1(E_161))), inference(resolution, [status(thm)], [c_70, c_1938])).
% 7.15/2.44  tff(c_3354, plain, (![A_230, B_231, E_232]: (k1_partfun1(A_230, B_231, '#skF_2', '#skF_1', E_232, '#skF_4')=k5_relat_1(E_232, '#skF_4') | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))) | ~v1_funct_1(E_232))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1944])).
% 7.15/2.44  tff(c_3360, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_3354])).
% 7.15/2.44  tff(c_3367, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1478, c_3360])).
% 7.15/2.44  tff(c_6, plain, (![A_6, B_10, C_12]: (k5_relat_1(k5_relat_1(A_6, B_10), C_12)=k5_relat_1(A_6, k5_relat_1(B_10, C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.15/2.44  tff(c_3383, plain, (![C_12]: (k5_relat_1(k6_partfun1('#skF_1'), C_12)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3367, c_6])).
% 7.15/2.44  tff(c_3393, plain, (![C_12]: (k5_relat_1(k6_partfun1('#skF_1'), C_12)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_12)) | ~v1_relat_1(C_12))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_123, c_3383])).
% 7.15/2.44  tff(c_4813, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4807, c_3393])).
% 7.15/2.44  tff(c_4829, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3601, c_227, c_3302, c_4813])).
% 7.15/2.44  tff(c_24, plain, (![A_18]: (k2_funct_1(k2_funct_1(A_18))=A_18 | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.15/2.44  tff(c_4864, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4829, c_24])).
% 7.15/2.44  tff(c_4882, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_74, c_3303, c_4864])).
% 7.15/2.44  tff(c_4884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4882])).
% 7.15/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/2.44  
% 7.15/2.44  Inference rules
% 7.15/2.44  ----------------------
% 7.15/2.44  #Ref     : 0
% 7.15/2.44  #Sup     : 1058
% 7.15/2.44  #Fact    : 0
% 7.15/2.44  #Define  : 0
% 7.15/2.44  #Split   : 18
% 7.15/2.44  #Chain   : 0
% 7.15/2.44  #Close   : 0
% 7.15/2.44  
% 7.15/2.44  Ordering : KBO
% 7.15/2.44  
% 7.15/2.44  Simplification rules
% 7.15/2.44  ----------------------
% 7.15/2.44  #Subsume      : 15
% 7.15/2.44  #Demod        : 1428
% 7.15/2.44  #Tautology    : 462
% 7.15/2.44  #SimpNegUnit  : 49
% 7.15/2.44  #BackRed      : 31
% 7.15/2.44  
% 7.15/2.44  #Partial instantiations: 0
% 7.15/2.44  #Strategies tried      : 1
% 7.15/2.44  
% 7.15/2.44  Timing (in seconds)
% 7.15/2.44  ----------------------
% 7.15/2.45  Preprocessing        : 0.40
% 7.15/2.45  Parsing              : 0.21
% 7.15/2.45  CNF conversion       : 0.03
% 7.15/2.45  Main loop            : 1.26
% 7.15/2.45  Inferencing          : 0.42
% 7.15/2.45  Reduction            : 0.49
% 7.15/2.45  Demodulation         : 0.37
% 7.15/2.45  BG Simplification    : 0.05
% 7.15/2.45  Subsumption          : 0.20
% 7.15/2.45  Abstraction          : 0.07
% 7.15/2.45  MUC search           : 0.00
% 7.15/2.45  Cooper               : 0.00
% 7.15/2.45  Total                : 1.71
% 7.15/2.45  Index Insertion      : 0.00
% 7.15/2.45  Index Deletion       : 0.00
% 7.15/2.45  Index Matching       : 0.00
% 7.15/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
