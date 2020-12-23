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
% DateTime   : Thu Dec  3 10:23:26 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  146 (3349 expanded)
%              Number of leaves         :   40 (1188 expanded)
%              Depth                    :   17
%              Number of atoms          :  264 (10071 expanded)
%              Number of equality atoms :   79 (3206 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_56,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_56])).

tff(c_50,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_63,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_56])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_87,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_44])).

tff(c_88,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_87,c_88])).

tff(c_94,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_91])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_40,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_535,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_539,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_535])).

tff(c_42,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_95,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_42])).

tff(c_540,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_95])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_74,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_80,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_74])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80])).

tff(c_85,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_84])).

tff(c_549,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_85])).

tff(c_500,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_504,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_87,c_500])).

tff(c_518,plain,(
    ! [B_100,A_101] :
      ( k1_relat_1(B_100) = A_101
      | ~ v1_partfun1(B_100,A_101)
      | ~ v4_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_521,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_504,c_518])).

tff(c_524,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_521])).

tff(c_534,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_73,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_46])).

tff(c_550,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_73])).

tff(c_548,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_87])).

tff(c_605,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_partfun1(C_109,A_110)
      | ~ v1_funct_2(C_109,A_110,B_111)
      | ~ v1_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | v1_xboole_0(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_608,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_548,c_605])).

tff(c_611,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_550,c_608])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_549,c_534,c_611])).

tff(c_614,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_619,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_87])).

tff(c_680,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_684,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_619,c_680])).

tff(c_618,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_95])).

tff(c_685,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_618])).

tff(c_621,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_73])).

tff(c_701,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_621])).

tff(c_698,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_684])).

tff(c_700,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_619])).

tff(c_797,plain,(
    ! [C_131,B_132,A_133] :
      ( m1_subset_1(k2_funct_1(C_131),k1_zfmisc_1(k2_zfmisc_1(B_132,A_133)))
      | k2_relset_1(A_133,B_132,C_131) != B_132
      | ~ v2_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132)))
      | ~ v1_funct_2(C_131,A_133,B_132)
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( k2_relset_1(A_13,B_14,C_15) = k2_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_971,plain,(
    ! [B_150,A_151,C_152] :
      ( k2_relset_1(B_150,A_151,k2_funct_1(C_152)) = k2_relat_1(k2_funct_1(C_152))
      | k2_relset_1(A_151,B_150,C_152) != B_150
      | ~ v2_funct_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150)))
      | ~ v1_funct_2(C_152,A_151,B_150)
      | ~ v1_funct_1(C_152) ) ),
    inference(resolution,[status(thm)],[c_797,c_16])).

tff(c_977,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_700,c_971])).

tff(c_981,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_701,c_40,c_698,c_977])).

tff(c_784,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_tops_2(A_128,B_129,C_130) = k2_funct_1(C_130)
      | ~ v2_funct_1(C_130)
      | k2_relset_1(A_128,B_129,C_130) != B_129
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_2(C_130,A_128,B_129)
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_787,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_700,c_784])).

tff(c_790,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_701,c_698,c_40,c_787])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_151,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_155,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_151])).

tff(c_156,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_95])).

tff(c_166,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_85])).

tff(c_107,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_87,c_107])).

tff(c_122,plain,(
    ! [B_48,A_49] :
      ( k1_relat_1(B_48) = A_49
      | ~ v1_partfun1(B_48,A_49)
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_125,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_122])).

tff(c_128,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_125])).

tff(c_129,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_167,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_73])).

tff(c_165,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_87])).

tff(c_18,plain,(
    ! [C_19,A_16,B_17] :
      ( v1_partfun1(C_19,A_16)
      | ~ v1_funct_2(C_19,A_16,B_17)
      | ~ v1_funct_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | v1_xboole_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_194,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_165,c_18])).

tff(c_212,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_167,c_194])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_129,c_212])).

tff(c_215,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_219,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_87])).

tff(c_283,plain,(
    ! [A_61,B_62,C_63] :
      ( k2_relset_1(A_61,B_62,C_63) = k2_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_287,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_219,c_283])).

tff(c_218,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_95])).

tff(c_288,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_218])).

tff(c_221,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_73])).

tff(c_300,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_221])).

tff(c_298,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_287])).

tff(c_299,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_219])).

tff(c_392,plain,(
    ! [C_80,B_81,A_82] :
      ( m1_subset_1(k2_funct_1(C_80),k1_zfmisc_1(k2_zfmisc_1(B_81,A_82)))
      | k2_relset_1(A_82,B_81,C_80) != B_81
      | ~ v2_funct_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81)))
      | ~ v1_funct_2(C_80,A_82,B_81)
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_471,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_relset_1(B_92,A_93,k2_funct_1(C_94)) = k1_relat_1(k2_funct_1(C_94))
      | k2_relset_1(A_93,B_92,C_94) != B_92
      | ~ v2_funct_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ v1_funct_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_392,c_14])).

tff(c_477,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_299,c_471])).

tff(c_481,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_300,c_40,c_298,c_477])).

tff(c_380,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_tops_2(A_77,B_78,C_79) = k2_funct_1(C_79)
      | ~ v2_funct_1(C_79)
      | k2_relset_1(A_77,B_78,C_79) != B_78
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_2(C_79,A_77,B_78)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_383,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_299,c_380])).

tff(c_386,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_300,c_298,c_40,c_383])).

tff(c_38,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_105,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_63,c_63,c_64,c_64,c_63,c_63,c_38])).

tff(c_106,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_361,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_288,c_288,c_215,c_215,c_106])).

tff(c_387,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_361])).

tff(c_482,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_387])).

tff(c_489,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_482])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_48,c_40,c_489])).

tff(c_494,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_767,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_685,c_614,c_614,c_614,c_494])).

tff(c_792,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_767])).

tff(c_982,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_792])).

tff(c_989,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_982])).

tff(c_993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_48,c_40,c_989])).
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
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.49  
% 3.32/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.32/1.49  
% 3.32/1.49  %Foreground sorts:
% 3.32/1.49  
% 3.32/1.49  
% 3.32/1.49  %Background operators:
% 3.32/1.49  
% 3.32/1.49  
% 3.32/1.49  %Foreground operators:
% 3.32/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.32/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.32/1.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.32/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.49  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.32/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.49  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.32/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.32/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.32/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.32/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.32/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.32/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.49  
% 3.32/1.52  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.32/1.52  tff(f_144, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.32/1.52  tff(f_100, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.32/1.52  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.32/1.52  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.32/1.52  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.32/1.52  tff(f_108, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.32/1.52  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.32/1.52  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.32/1.52  tff(f_72, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.32/1.52  tff(f_96, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.32/1.52  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.32/1.52  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.32/1.52  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.52  tff(c_54, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_56, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.32/1.52  tff(c_64, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_56])).
% 3.32/1.52  tff(c_50, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_63, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_56])).
% 3.32/1.52  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_87, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_44])).
% 3.32/1.52  tff(c_88, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.52  tff(c_91, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_87, c_88])).
% 3.32/1.52  tff(c_94, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_91])).
% 3.32/1.52  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_40, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.32/1.52  tff(c_535, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.32/1.52  tff(c_539, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_87, c_535])).
% 3.32/1.52  tff(c_42, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_95, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_42])).
% 3.32/1.52  tff(c_540, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_95])).
% 3.32/1.52  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_74, plain, (![A_37]: (~v1_xboole_0(u1_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.52  tff(c_80, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_63, c_74])).
% 3.32/1.52  tff(c_84, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80])).
% 3.32/1.52  tff(c_85, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_84])).
% 3.32/1.52  tff(c_549, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_85])).
% 3.32/1.52  tff(c_500, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.32/1.52  tff(c_504, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_87, c_500])).
% 3.32/1.52  tff(c_518, plain, (![B_100, A_101]: (k1_relat_1(B_100)=A_101 | ~v1_partfun1(B_100, A_101) | ~v4_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.32/1.52  tff(c_521, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_504, c_518])).
% 3.32/1.52  tff(c_524, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_521])).
% 3.32/1.52  tff(c_534, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_524])).
% 3.32/1.52  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_73, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_46])).
% 3.32/1.52  tff(c_550, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_73])).
% 3.32/1.52  tff(c_548, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_87])).
% 3.32/1.52  tff(c_605, plain, (![C_109, A_110, B_111]: (v1_partfun1(C_109, A_110) | ~v1_funct_2(C_109, A_110, B_111) | ~v1_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | v1_xboole_0(B_111))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.52  tff(c_608, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_548, c_605])).
% 3.32/1.52  tff(c_611, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_550, c_608])).
% 3.32/1.52  tff(c_613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_549, c_534, c_611])).
% 3.32/1.52  tff(c_614, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_524])).
% 3.32/1.52  tff(c_619, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_87])).
% 3.32/1.52  tff(c_680, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.32/1.52  tff(c_684, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_619, c_680])).
% 3.32/1.52  tff(c_618, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_614, c_95])).
% 3.32/1.52  tff(c_685, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_684, c_618])).
% 3.32/1.52  tff(c_621, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_73])).
% 3.32/1.52  tff(c_701, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_685, c_621])).
% 3.32/1.52  tff(c_698, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_685, c_684])).
% 3.32/1.52  tff(c_700, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_685, c_619])).
% 3.32/1.52  tff(c_797, plain, (![C_131, B_132, A_133]: (m1_subset_1(k2_funct_1(C_131), k1_zfmisc_1(k2_zfmisc_1(B_132, A_133))) | k2_relset_1(A_133, B_132, C_131)!=B_132 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))) | ~v1_funct_2(C_131, A_133, B_132) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.52  tff(c_16, plain, (![A_13, B_14, C_15]: (k2_relset_1(A_13, B_14, C_15)=k2_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.32/1.52  tff(c_971, plain, (![B_150, A_151, C_152]: (k2_relset_1(B_150, A_151, k2_funct_1(C_152))=k2_relat_1(k2_funct_1(C_152)) | k2_relset_1(A_151, B_150, C_152)!=B_150 | ~v2_funct_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))) | ~v1_funct_2(C_152, A_151, B_150) | ~v1_funct_1(C_152))), inference(resolution, [status(thm)], [c_797, c_16])).
% 3.32/1.52  tff(c_977, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_700, c_971])).
% 3.32/1.52  tff(c_981, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_701, c_40, c_698, c_977])).
% 3.32/1.52  tff(c_784, plain, (![A_128, B_129, C_130]: (k2_tops_2(A_128, B_129, C_130)=k2_funct_1(C_130) | ~v2_funct_1(C_130) | k2_relset_1(A_128, B_129, C_130)!=B_129 | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_2(C_130, A_128, B_129) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.32/1.52  tff(c_787, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_700, c_784])).
% 3.32/1.52  tff(c_790, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_701, c_698, c_40, c_787])).
% 3.32/1.52  tff(c_8, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.32/1.52  tff(c_151, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.32/1.52  tff(c_155, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_87, c_151])).
% 3.32/1.52  tff(c_156, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_95])).
% 3.32/1.52  tff(c_166, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_85])).
% 3.32/1.52  tff(c_107, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.32/1.52  tff(c_111, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_87, c_107])).
% 3.32/1.52  tff(c_122, plain, (![B_48, A_49]: (k1_relat_1(B_48)=A_49 | ~v1_partfun1(B_48, A_49) | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.32/1.52  tff(c_125, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_111, c_122])).
% 3.32/1.52  tff(c_128, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_125])).
% 3.32/1.52  tff(c_129, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_128])).
% 3.32/1.52  tff(c_167, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_73])).
% 3.32/1.52  tff(c_165, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_87])).
% 3.32/1.52  tff(c_18, plain, (![C_19, A_16, B_17]: (v1_partfun1(C_19, A_16) | ~v1_funct_2(C_19, A_16, B_17) | ~v1_funct_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | v1_xboole_0(B_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.32/1.52  tff(c_194, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_165, c_18])).
% 3.32/1.52  tff(c_212, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_167, c_194])).
% 3.32/1.52  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_129, c_212])).
% 3.32/1.52  tff(c_215, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_128])).
% 3.32/1.52  tff(c_219, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_87])).
% 3.32/1.52  tff(c_283, plain, (![A_61, B_62, C_63]: (k2_relset_1(A_61, B_62, C_63)=k2_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.32/1.52  tff(c_287, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_219, c_283])).
% 3.32/1.52  tff(c_218, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_95])).
% 3.32/1.52  tff(c_288, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_218])).
% 3.32/1.52  tff(c_221, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_73])).
% 3.32/1.52  tff(c_300, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_221])).
% 3.32/1.52  tff(c_298, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_287])).
% 3.32/1.52  tff(c_299, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_219])).
% 3.32/1.52  tff(c_392, plain, (![C_80, B_81, A_82]: (m1_subset_1(k2_funct_1(C_80), k1_zfmisc_1(k2_zfmisc_1(B_81, A_82))) | k2_relset_1(A_82, B_81, C_80)!=B_81 | ~v2_funct_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))) | ~v1_funct_2(C_80, A_82, B_81) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.52  tff(c_14, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.32/1.52  tff(c_471, plain, (![B_92, A_93, C_94]: (k1_relset_1(B_92, A_93, k2_funct_1(C_94))=k1_relat_1(k2_funct_1(C_94)) | k2_relset_1(A_93, B_92, C_94)!=B_92 | ~v2_funct_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_94, A_93, B_92) | ~v1_funct_1(C_94))), inference(resolution, [status(thm)], [c_392, c_14])).
% 3.32/1.52  tff(c_477, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_299, c_471])).
% 3.32/1.52  tff(c_481, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_300, c_40, c_298, c_477])).
% 3.32/1.52  tff(c_380, plain, (![A_77, B_78, C_79]: (k2_tops_2(A_77, B_78, C_79)=k2_funct_1(C_79) | ~v2_funct_1(C_79) | k2_relset_1(A_77, B_78, C_79)!=B_78 | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_2(C_79, A_77, B_78) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.32/1.52  tff(c_383, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_299, c_380])).
% 3.32/1.52  tff(c_386, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_300, c_298, c_40, c_383])).
% 3.32/1.52  tff(c_38, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.32/1.52  tff(c_105, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_63, c_63, c_64, c_64, c_63, c_63, c_38])).
% 3.32/1.52  tff(c_106, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_105])).
% 3.32/1.52  tff(c_361, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_288, c_288, c_215, c_215, c_106])).
% 3.32/1.52  tff(c_387, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_361])).
% 3.32/1.52  tff(c_482, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_481, c_387])).
% 3.32/1.52  tff(c_489, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_482])).
% 3.32/1.52  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_48, c_40, c_489])).
% 3.32/1.52  tff(c_494, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_105])).
% 3.32/1.52  tff(c_767, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_685, c_685, c_614, c_614, c_614, c_494])).
% 3.32/1.52  tff(c_792, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_767])).
% 3.32/1.52  tff(c_982, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_792])).
% 3.32/1.52  tff(c_989, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_982])).
% 3.32/1.52  tff(c_993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_48, c_40, c_989])).
% 3.32/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.52  
% 3.32/1.52  Inference rules
% 3.32/1.52  ----------------------
% 3.32/1.52  #Ref     : 0
% 3.32/1.52  #Sup     : 213
% 3.32/1.52  #Fact    : 0
% 3.32/1.52  #Define  : 0
% 3.32/1.52  #Split   : 6
% 3.32/1.52  #Chain   : 0
% 3.32/1.52  #Close   : 0
% 3.32/1.52  
% 3.32/1.52  Ordering : KBO
% 3.32/1.52  
% 3.32/1.52  Simplification rules
% 3.32/1.52  ----------------------
% 3.32/1.52  #Subsume      : 6
% 3.32/1.52  #Demod        : 256
% 3.32/1.52  #Tautology    : 129
% 3.32/1.52  #SimpNegUnit  : 10
% 3.32/1.52  #BackRed      : 50
% 3.32/1.52  
% 3.32/1.52  #Partial instantiations: 0
% 3.32/1.52  #Strategies tried      : 1
% 3.32/1.52  
% 3.32/1.52  Timing (in seconds)
% 3.32/1.52  ----------------------
% 3.32/1.52  Preprocessing        : 0.34
% 3.32/1.52  Parsing              : 0.18
% 3.32/1.52  CNF conversion       : 0.02
% 3.32/1.52  Main loop            : 0.41
% 3.32/1.52  Inferencing          : 0.14
% 3.32/1.52  Reduction            : 0.14
% 3.32/1.52  Demodulation         : 0.10
% 3.32/1.52  BG Simplification    : 0.02
% 3.32/1.52  Subsumption          : 0.06
% 3.32/1.52  Abstraction          : 0.02
% 3.32/1.52  MUC search           : 0.00
% 3.32/1.52  Cooper               : 0.00
% 3.32/1.52  Total                : 0.80
% 3.32/1.52  Index Insertion      : 0.00
% 3.32/1.52  Index Deletion       : 0.00
% 3.32/1.52  Index Matching       : 0.00
% 3.32/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
