%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:04 EST 2020

% Result     : Theorem 6.44s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 578 expanded)
%              Number of leaves         :   45 ( 227 expanded)
%              Depth                    :   13
%              Number of atoms          :  369 (2415 expanded)
%              Number of equality atoms :  124 ( 831 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_58,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

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

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_62,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_154,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_166,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_154])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_216,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_230,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_216])).

tff(c_2107,plain,(
    ! [B_171,C_172,A_173] :
      ( k6_partfun1(B_171) = k5_relat_1(k2_funct_1(C_172),C_172)
      | k1_xboole_0 = B_171
      | ~ v2_funct_1(C_172)
      | k2_relset_1(A_173,B_171,C_172) != B_171
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_173,B_171)))
      | ~ v1_funct_2(C_172,A_173,B_171)
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_2113,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_2107])).

tff(c_2123,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_230,c_2113])).

tff(c_2124,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2123])).

tff(c_2168,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2124])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_42,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_191,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_198,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_42,c_191])).

tff(c_899,plain,(
    ! [B_115,D_119,F_116,A_118,C_117,E_114] :
      ( k1_partfun1(A_118,B_115,C_117,D_119,E_114,F_116) = k5_relat_1(E_114,F_116)
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_117,D_119)))
      | ~ v1_funct_1(F_116)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_118,B_115)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_905,plain,(
    ! [A_118,B_115,E_114] :
      ( k1_partfun1(A_118,B_115,'#skF_2','#skF_1',E_114,'#skF_4') = k5_relat_1(E_114,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_118,B_115)))
      | ~ v1_funct_1(E_114) ) ),
    inference(resolution,[status(thm)],[c_74,c_899])).

tff(c_966,plain,(
    ! [A_121,B_122,E_123] :
      ( k1_partfun1(A_121,B_122,'#skF_2','#skF_1',E_123,'#skF_4') = k5_relat_1(E_123,'#skF_4')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_1(E_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_905])).

tff(c_972,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_966])).

tff(c_979,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_972])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_404,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_412,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_404])).

tff(c_427,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_412])).

tff(c_580,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_1009,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_580])).

tff(c_1316,plain,(
    ! [C_137,E_140,F_138,A_136,D_135,B_139] :
      ( m1_subset_1(k1_partfun1(A_136,B_139,C_137,D_135,E_140,F_138),k1_zfmisc_1(k2_zfmisc_1(A_136,D_135)))
      | ~ m1_subset_1(F_138,k1_zfmisc_1(k2_zfmisc_1(C_137,D_135)))
      | ~ v1_funct_1(F_138)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_136,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1350,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_1316])).

tff(c_1365,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_1350])).

tff(c_1367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1009,c_1365])).

tff(c_1368,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_3324,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( k2_relset_1(A_215,B_216,C_217) = B_216
      | ~ r2_relset_1(B_216,B_216,k1_partfun1(B_216,A_215,A_215,B_216,D_218,C_217),k6_partfun1(B_216))
      | ~ m1_subset_1(D_218,k1_zfmisc_1(k2_zfmisc_1(B_216,A_215)))
      | ~ v1_funct_2(D_218,B_216,A_215)
      | ~ v1_funct_1(D_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_2(C_217,A_215,B_216)
      | ~ v1_funct_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3330,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_3324])).

tff(c_3334,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_84,c_82,c_80,c_198,c_230,c_3330])).

tff(c_3336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2168,c_3334])).

tff(c_3337,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2124])).

tff(c_3382,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3337])).

tff(c_46,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_18,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_18])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_4222,plain,(
    ! [B_252,D_250,A_254,E_253,C_251] :
      ( k1_xboole_0 = C_251
      | v2_funct_1(E_253)
      | k2_relset_1(A_254,B_252,D_250) != B_252
      | ~ v2_funct_1(k1_partfun1(A_254,B_252,B_252,C_251,D_250,E_253))
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(B_252,C_251)))
      | ~ v1_funct_2(E_253,B_252,C_251)
      | ~ v1_funct_1(E_253)
      | ~ m1_subset_1(D_250,k1_zfmisc_1(k2_zfmisc_1(A_254,B_252)))
      | ~ v1_funct_2(D_250,A_254,B_252)
      | ~ v1_funct_1(D_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4226,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1368,c_4222])).

tff(c_4231,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_85,c_72,c_4226])).

tff(c_4233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3382,c_66,c_4231])).

tff(c_4235,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3337])).

tff(c_6,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_89,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_3338,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2124])).

tff(c_3339,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3338,c_230])).

tff(c_4360,plain,(
    ! [A_259,C_260,B_261] :
      ( k6_partfun1(A_259) = k5_relat_1(C_260,k2_funct_1(C_260))
      | k1_xboole_0 = B_261
      | ~ v2_funct_1(C_260)
      | k2_relset_1(A_259,B_261,C_260) != B_261
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_259,B_261)))
      | ~ v1_funct_2(C_260,A_259,B_261)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_4366,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_4360])).

tff(c_4376,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_3339,c_4235,c_4366])).

tff(c_4377,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4376])).

tff(c_26,plain,(
    ! [A_14] :
      ( k1_relat_1(k5_relat_1(A_14,k2_funct_1(A_14))) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4456,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4377,c_26])).

tff(c_4467,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_78,c_4235,c_89,c_4456])).

tff(c_164,plain,(
    ! [A_31] : v1_relat_1(k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_42,c_154])).

tff(c_12,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_3352,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3338,c_86])).

tff(c_3362,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_3352])).

tff(c_10,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_87,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_281,plain,(
    ! [A_81,B_82,C_83] :
      ( k5_relat_1(k5_relat_1(A_81,B_82),C_83) = k5_relat_1(A_81,k5_relat_1(B_82,C_83))
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_314,plain,(
    ! [A_9,C_83] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_83)) = k5_relat_1(A_9,C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(A_9)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_281])).

tff(c_331,plain,(
    ! [A_9,C_83] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_83)) = k5_relat_1(A_9,C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_314])).

tff(c_3371,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3362,c_331])).

tff(c_3378,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_164,c_3362,c_3371])).

tff(c_4471,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4467,c_3378])).

tff(c_165,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_154])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_222,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_216])).

tff(c_229,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_222])).

tff(c_167,plain,(
    ! [A_67] :
      ( k1_relat_1(k2_funct_1(A_67)) = k2_relat_1(A_67)
      | ~ v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1716,plain,(
    ! [A_148] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_148)),k2_funct_1(A_148)) = k2_funct_1(A_148)
      | ~ v1_relat_1(k2_funct_1(A_148))
      | ~ v2_funct_1(A_148)
      | ~ v1_funct_1(A_148)
      | ~ v1_relat_1(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_87])).

tff(c_1740,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_1716])).

tff(c_1756,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_84,c_68,c_1740])).

tff(c_1773,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1756])).

tff(c_1776,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1773])).

tff(c_1780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_84,c_1776])).

tff(c_1782,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1756])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_4364,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_4360])).

tff(c_4372,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_4364])).

tff(c_4373,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4372])).

tff(c_4393,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4373,c_26])).

tff(c_4408,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_84,c_68,c_89,c_4393])).

tff(c_204,plain,(
    ! [A_74] :
      ( k2_relat_1(k2_funct_1(A_74)) = k1_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_210,plain,(
    ! [A_74] :
      ( k5_relat_1(k2_funct_1(A_74),k6_partfun1(k1_relat_1(A_74))) = k2_funct_1(A_74)
      | ~ v1_relat_1(k2_funct_1(A_74))
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_86])).

tff(c_4420,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4408,c_210])).

tff(c_4436,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_84,c_68,c_1782,c_4420])).

tff(c_1871,plain,(
    ! [B_161,C_163,F_162,D_165,A_164,E_160] :
      ( k1_partfun1(A_164,B_161,C_163,D_165,E_160,F_162) = k5_relat_1(E_160,F_162)
      | ~ m1_subset_1(F_162,k1_zfmisc_1(k2_zfmisc_1(C_163,D_165)))
      | ~ v1_funct_1(F_162)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(A_164,B_161)))
      | ~ v1_funct_1(E_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1877,plain,(
    ! [A_164,B_161,E_160] :
      ( k1_partfun1(A_164,B_161,'#skF_2','#skF_1',E_160,'#skF_4') = k5_relat_1(E_160,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(A_164,B_161)))
      | ~ v1_funct_1(E_160) ) ),
    inference(resolution,[status(thm)],[c_74,c_1871])).

tff(c_4607,plain,(
    ! [A_268,B_269,E_270] :
      ( k1_partfun1(A_268,B_269,'#skF_2','#skF_1',E_270,'#skF_4') = k5_relat_1(E_270,'#skF_4')
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269)))
      | ~ v1_funct_1(E_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1877])).

tff(c_4616,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_4607])).

tff(c_4624,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1368,c_4616])).

tff(c_2111,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_2107])).

tff(c_2119,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_2111])).

tff(c_2120,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2119])).

tff(c_4,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2134,plain,(
    ! [C_7] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_7)) = k5_relat_1(k6_partfun1('#skF_2'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2120,c_4])).

tff(c_5392,plain,(
    ! [C_298] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_298)) = k5_relat_1(k6_partfun1('#skF_2'),C_298)
      | ~ v1_relat_1(C_298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1782,c_165,c_2134])).

tff(c_5410,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4624,c_5392])).

tff(c_5435,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_4471,c_4436,c_5410])).

tff(c_5437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:42:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.44/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.30  
% 6.66/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.30  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.66/2.30  
% 6.66/2.30  %Foreground sorts:
% 6.66/2.30  
% 6.66/2.30  
% 6.66/2.30  %Background operators:
% 6.66/2.30  
% 6.66/2.30  
% 6.66/2.30  %Foreground operators:
% 6.66/2.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.66/2.30  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 6.66/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.66/2.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.66/2.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.66/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.66/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.66/2.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.66/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.66/2.30  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.66/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.66/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.66/2.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.66/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.66/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.66/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.66/2.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.66/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.66/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.66/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.66/2.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.66/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.66/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.66/2.30  
% 6.66/2.32  tff(f_207, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.66/2.32  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.66/2.32  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.66/2.32  tff(f_181, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 6.66/2.32  tff(f_110, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.66/2.32  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.66/2.32  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.66/2.32  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.66/2.32  tff(f_139, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.66/2.32  tff(f_122, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.66/2.32  tff(f_58, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 6.66/2.32  tff(f_165, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 6.66/2.32  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.66/2.32  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 6.66/2.32  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 6.66/2.32  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.66/2.32  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.66/2.32  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.66/2.32  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.66/2.32  tff(c_62, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_154, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.66/2.32  tff(c_166, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_154])).
% 6.66/2.32  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_66, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_216, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.66/2.32  tff(c_230, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_216])).
% 6.66/2.32  tff(c_2107, plain, (![B_171, C_172, A_173]: (k6_partfun1(B_171)=k5_relat_1(k2_funct_1(C_172), C_172) | k1_xboole_0=B_171 | ~v2_funct_1(C_172) | k2_relset_1(A_173, B_171, C_172)!=B_171 | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_173, B_171))) | ~v1_funct_2(C_172, A_173, B_171) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.66/2.32  tff(c_2113, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_2107])).
% 6.66/2.32  tff(c_2123, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_230, c_2113])).
% 6.66/2.32  tff(c_2124, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_66, c_2123])).
% 6.66/2.32  tff(c_2168, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2124])).
% 6.66/2.32  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_42, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.66/2.32  tff(c_191, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.66/2.32  tff(c_198, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_42, c_191])).
% 6.66/2.32  tff(c_899, plain, (![B_115, D_119, F_116, A_118, C_117, E_114]: (k1_partfun1(A_118, B_115, C_117, D_119, E_114, F_116)=k5_relat_1(E_114, F_116) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_117, D_119))) | ~v1_funct_1(F_116) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_118, B_115))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.66/2.32  tff(c_905, plain, (![A_118, B_115, E_114]: (k1_partfun1(A_118, B_115, '#skF_2', '#skF_1', E_114, '#skF_4')=k5_relat_1(E_114, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_118, B_115))) | ~v1_funct_1(E_114))), inference(resolution, [status(thm)], [c_74, c_899])).
% 6.66/2.32  tff(c_966, plain, (![A_121, B_122, E_123]: (k1_partfun1(A_121, B_122, '#skF_2', '#skF_1', E_123, '#skF_4')=k5_relat_1(E_123, '#skF_4') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_1(E_123))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_905])).
% 6.66/2.32  tff(c_972, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_966])).
% 6.66/2.32  tff(c_979, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_972])).
% 6.66/2.32  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_404, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.66/2.32  tff(c_412, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_404])).
% 6.66/2.32  tff(c_427, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_412])).
% 6.66/2.32  tff(c_580, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_427])).
% 6.66/2.32  tff(c_1009, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_979, c_580])).
% 6.66/2.32  tff(c_1316, plain, (![C_137, E_140, F_138, A_136, D_135, B_139]: (m1_subset_1(k1_partfun1(A_136, B_139, C_137, D_135, E_140, F_138), k1_zfmisc_1(k2_zfmisc_1(A_136, D_135))) | ~m1_subset_1(F_138, k1_zfmisc_1(k2_zfmisc_1(C_137, D_135))) | ~v1_funct_1(F_138) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_136, B_139))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.66/2.32  tff(c_1350, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_979, c_1316])).
% 6.66/2.32  tff(c_1365, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_1350])).
% 6.66/2.32  tff(c_1367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1009, c_1365])).
% 6.66/2.32  tff(c_1368, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_427])).
% 6.66/2.32  tff(c_3324, plain, (![A_215, B_216, C_217, D_218]: (k2_relset_1(A_215, B_216, C_217)=B_216 | ~r2_relset_1(B_216, B_216, k1_partfun1(B_216, A_215, A_215, B_216, D_218, C_217), k6_partfun1(B_216)) | ~m1_subset_1(D_218, k1_zfmisc_1(k2_zfmisc_1(B_216, A_215))) | ~v1_funct_2(D_218, B_216, A_215) | ~v1_funct_1(D_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_2(C_217, A_215, B_216) | ~v1_funct_1(C_217))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.66/2.32  tff(c_3330, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1368, c_3324])).
% 6.66/2.32  tff(c_3334, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_84, c_82, c_80, c_198, c_230, c_3330])).
% 6.66/2.32  tff(c_3336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2168, c_3334])).
% 6.66/2.32  tff(c_3337, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2124])).
% 6.66/2.32  tff(c_3382, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3337])).
% 6.66/2.32  tff(c_46, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.66/2.32  tff(c_18, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.66/2.32  tff(c_85, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_18])).
% 6.66/2.32  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_4222, plain, (![B_252, D_250, A_254, E_253, C_251]: (k1_xboole_0=C_251 | v2_funct_1(E_253) | k2_relset_1(A_254, B_252, D_250)!=B_252 | ~v2_funct_1(k1_partfun1(A_254, B_252, B_252, C_251, D_250, E_253)) | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(B_252, C_251))) | ~v1_funct_2(E_253, B_252, C_251) | ~v1_funct_1(E_253) | ~m1_subset_1(D_250, k1_zfmisc_1(k2_zfmisc_1(A_254, B_252))) | ~v1_funct_2(D_250, A_254, B_252) | ~v1_funct_1(D_250))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.66/2.32  tff(c_4226, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1368, c_4222])).
% 6.66/2.32  tff(c_4231, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_85, c_72, c_4226])).
% 6.66/2.32  tff(c_4233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3382, c_66, c_4231])).
% 6.66/2.32  tff(c_4235, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3337])).
% 6.66/2.32  tff(c_6, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.66/2.32  tff(c_89, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 6.66/2.32  tff(c_3338, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2124])).
% 6.66/2.32  tff(c_3339, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3338, c_230])).
% 6.66/2.32  tff(c_4360, plain, (![A_259, C_260, B_261]: (k6_partfun1(A_259)=k5_relat_1(C_260, k2_funct_1(C_260)) | k1_xboole_0=B_261 | ~v2_funct_1(C_260) | k2_relset_1(A_259, B_261, C_260)!=B_261 | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_259, B_261))) | ~v1_funct_2(C_260, A_259, B_261) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.66/2.32  tff(c_4366, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_4360])).
% 6.66/2.32  tff(c_4376, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_3339, c_4235, c_4366])).
% 6.66/2.32  tff(c_4377, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_4376])).
% 6.66/2.32  tff(c_26, plain, (![A_14]: (k1_relat_1(k5_relat_1(A_14, k2_funct_1(A_14)))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.66/2.32  tff(c_4456, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4377, c_26])).
% 6.66/2.32  tff(c_4467, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_78, c_4235, c_89, c_4456])).
% 6.66/2.32  tff(c_164, plain, (![A_31]: (v1_relat_1(k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_42, c_154])).
% 6.66/2.32  tff(c_12, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.66/2.32  tff(c_86, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 6.66/2.32  tff(c_3352, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3338, c_86])).
% 6.66/2.32  tff(c_3362, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_3352])).
% 6.66/2.32  tff(c_10, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.66/2.32  tff(c_87, plain, (![A_9]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 6.66/2.32  tff(c_281, plain, (![A_81, B_82, C_83]: (k5_relat_1(k5_relat_1(A_81, B_82), C_83)=k5_relat_1(A_81, k5_relat_1(B_82, C_83)) | ~v1_relat_1(C_83) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.66/2.32  tff(c_314, plain, (![A_9, C_83]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_83))=k5_relat_1(A_9, C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(A_9) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_87, c_281])).
% 6.66/2.32  tff(c_331, plain, (![A_9, C_83]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_83))=k5_relat_1(A_9, C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_314])).
% 6.66/2.32  tff(c_3371, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3362, c_331])).
% 6.66/2.32  tff(c_3378, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_164, c_3362, c_3371])).
% 6.66/2.32  tff(c_4471, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4467, c_3378])).
% 6.66/2.32  tff(c_165, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_154])).
% 6.66/2.32  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_16, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.66/2.32  tff(c_222, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_216])).
% 6.66/2.32  tff(c_229, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_222])).
% 6.66/2.32  tff(c_167, plain, (![A_67]: (k1_relat_1(k2_funct_1(A_67))=k2_relat_1(A_67) | ~v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.66/2.32  tff(c_1716, plain, (![A_148]: (k5_relat_1(k6_partfun1(k2_relat_1(A_148)), k2_funct_1(A_148))=k2_funct_1(A_148) | ~v1_relat_1(k2_funct_1(A_148)) | ~v2_funct_1(A_148) | ~v1_funct_1(A_148) | ~v1_relat_1(A_148))), inference(superposition, [status(thm), theory('equality')], [c_167, c_87])).
% 6.66/2.32  tff(c_1740, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_229, c_1716])).
% 6.66/2.32  tff(c_1756, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_84, c_68, c_1740])).
% 6.66/2.32  tff(c_1773, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1756])).
% 6.66/2.32  tff(c_1776, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1773])).
% 6.66/2.32  tff(c_1780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_84, c_1776])).
% 6.66/2.32  tff(c_1782, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1756])).
% 6.66/2.32  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.66/2.32  tff(c_4364, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_4360])).
% 6.66/2.32  tff(c_4372, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_4364])).
% 6.66/2.32  tff(c_4373, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_4372])).
% 6.66/2.32  tff(c_4393, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4373, c_26])).
% 6.66/2.32  tff(c_4408, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_84, c_68, c_89, c_4393])).
% 6.66/2.32  tff(c_204, plain, (![A_74]: (k2_relat_1(k2_funct_1(A_74))=k1_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.66/2.32  tff(c_210, plain, (![A_74]: (k5_relat_1(k2_funct_1(A_74), k6_partfun1(k1_relat_1(A_74)))=k2_funct_1(A_74) | ~v1_relat_1(k2_funct_1(A_74)) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_204, c_86])).
% 6.66/2.32  tff(c_4420, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4408, c_210])).
% 6.66/2.32  tff(c_4436, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_84, c_68, c_1782, c_4420])).
% 6.66/2.32  tff(c_1871, plain, (![B_161, C_163, F_162, D_165, A_164, E_160]: (k1_partfun1(A_164, B_161, C_163, D_165, E_160, F_162)=k5_relat_1(E_160, F_162) | ~m1_subset_1(F_162, k1_zfmisc_1(k2_zfmisc_1(C_163, D_165))) | ~v1_funct_1(F_162) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(A_164, B_161))) | ~v1_funct_1(E_160))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.66/2.32  tff(c_1877, plain, (![A_164, B_161, E_160]: (k1_partfun1(A_164, B_161, '#skF_2', '#skF_1', E_160, '#skF_4')=k5_relat_1(E_160, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(A_164, B_161))) | ~v1_funct_1(E_160))), inference(resolution, [status(thm)], [c_74, c_1871])).
% 6.66/2.32  tff(c_4607, plain, (![A_268, B_269, E_270]: (k1_partfun1(A_268, B_269, '#skF_2', '#skF_1', E_270, '#skF_4')=k5_relat_1(E_270, '#skF_4') | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))) | ~v1_funct_1(E_270))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1877])).
% 6.66/2.32  tff(c_4616, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_4607])).
% 6.66/2.32  tff(c_4624, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1368, c_4616])).
% 6.66/2.32  tff(c_2111, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_2107])).
% 6.66/2.32  tff(c_2119, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_2111])).
% 6.66/2.32  tff(c_2120, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_2119])).
% 6.66/2.32  tff(c_4, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.66/2.32  tff(c_2134, plain, (![C_7]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_7))=k5_relat_1(k6_partfun1('#skF_2'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2120, c_4])).
% 6.66/2.32  tff(c_5392, plain, (![C_298]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_298))=k5_relat_1(k6_partfun1('#skF_2'), C_298) | ~v1_relat_1(C_298))), inference(demodulation, [status(thm), theory('equality')], [c_1782, c_165, c_2134])).
% 6.66/2.32  tff(c_5410, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4624, c_5392])).
% 6.66/2.32  tff(c_5435, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_4471, c_4436, c_5410])).
% 6.66/2.32  tff(c_5437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_5435])).
% 6.66/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.32  
% 6.66/2.32  Inference rules
% 6.66/2.32  ----------------------
% 6.66/2.32  #Ref     : 0
% 6.66/2.32  #Sup     : 1143
% 6.66/2.32  #Fact    : 0
% 6.66/2.32  #Define  : 0
% 6.66/2.32  #Split   : 14
% 6.66/2.32  #Chain   : 0
% 6.66/2.32  #Close   : 0
% 6.66/2.32  
% 6.66/2.32  Ordering : KBO
% 6.66/2.32  
% 6.66/2.32  Simplification rules
% 6.66/2.32  ----------------------
% 6.66/2.32  #Subsume      : 39
% 6.66/2.32  #Demod        : 1854
% 6.66/2.32  #Tautology    : 628
% 6.66/2.32  #SimpNegUnit  : 43
% 6.66/2.32  #BackRed      : 48
% 6.66/2.32  
% 6.66/2.32  #Partial instantiations: 0
% 6.66/2.32  #Strategies tried      : 1
% 6.66/2.32  
% 6.66/2.32  Timing (in seconds)
% 6.66/2.32  ----------------------
% 6.66/2.33  Preprocessing        : 0.38
% 6.66/2.33  Parsing              : 0.20
% 6.66/2.33  CNF conversion       : 0.03
% 6.66/2.33  Main loop            : 1.16
% 6.66/2.33  Inferencing          : 0.41
% 6.66/2.33  Reduction            : 0.45
% 6.66/2.33  Demodulation         : 0.35
% 6.66/2.33  BG Simplification    : 0.05
% 6.66/2.33  Subsumption          : 0.18
% 6.66/2.33  Abstraction          : 0.06
% 6.66/2.33  MUC search           : 0.00
% 6.66/2.33  Cooper               : 0.00
% 6.66/2.33  Total                : 1.60
% 6.66/2.33  Index Insertion      : 0.00
% 6.66/2.33  Index Deletion       : 0.00
% 6.66/2.33  Index Matching       : 0.00
% 6.66/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
